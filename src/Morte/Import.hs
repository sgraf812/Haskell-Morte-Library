{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# OPTIONS_GHC -Wall #-}

{-| Morte lets you import external expressions located either in local files or
    hosted on network endpoints.

    To import a local file as an expression, just insert the path to the file,
    prepending a @./@ if the path is relative to the current directory.  For
    example, suppose we had the following three local files:

    > -- id
    > \(a : *) -> \(x : a) -> x

    > -- Bool
    > forall (Bool : *) -> forall (True : Bool) -> forall (False : Bool) -> Bool

    > -- True
    > \(Bool : *) -> \(True : Bool) -> \(False : Bool) -> True

    You could then reference them within a Morte expression using this syntax:

    > ./id ./Bool ./True

    ... which would embed their expressions directly within the syntax tree:

    > -- ... expands out to:
    > (\(a : *) -> \(x : a) -> x)
    >     (forall (Bool : *) -> forall (True : Bool) -> forall (False : Bool) -> True)
    >     (\(Bool : *) -> \(True : Bool) -> \(False : Bool) -> True)

    ... and which normalizes to:

    > λ(Bool : *) → λ(True : Bool) → λ(False : Bool) → True

    Imported expressions may contain imports of their own, too, which will
    continue to be resolved.  However, Morte will prevent cyclic imports.  For
    example, if you had these two files:

    > -- foo
    > ./bar

    > -- bar
    > ./foo

    ... Morte would throw the following exception if you tried to import @foo@:

    > morte:
    > ⤷ ./foo
    > ⤷ ./bar
    > Cyclic import: ./foo

    You can also import expressions hosted on network endpoints.  Just use the
    URL

    > http://host[:port]/path

    The compiler expects the downloaded expressions to be in the same format
    as local files, specifically UTF8-encoded source code text.

    For example, if our @id@ expression were hosted at @http://example.com/id@,
    then we would embed the expression within our code using:

    > http://example.com/id

    You can also reuse directory names as expressions.  If you provide a path
    to a local or remote directory then the compiler will look for a file named
    @\@@ within that directory and use that file to represent the directory.
-}

module Morte.Import (
    -- * Import
      Path (..)
    , load
    , asFullyResolved
    , Cycle(..)
    , ReferentiallyOpaque(..)
    , Imported(..)
    ) where

import Control.Exception (Exception, IOException, catch, onException, throwIO)
import Control.Monad (join)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.State.Strict (StateT)
import Data.Map.Strict (Map)
import Data.Monoid ((<>))
import Data.Text.Buildable (build)
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder (Builder)
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable (traverse)
#endif
import Data.Typeable (Typeable)
import Filesystem.Path ((</>), FilePath)
import Filesystem
import Lens.Micro (Lens')
import Lens.Micro.Mtl (zoom)
import Morte.Core (Expr)
import Morte.Path (Path(..), EmbedPath)
import Network.HTTP.Client (Manager)
import Prelude hiding (FilePath)

import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Foldable                    as Foldable
import qualified Data.List                        as List
import qualified Data.Map.Strict                  as Map
import qualified Data.Text.Lazy                   as Text
import qualified Data.Text.Lazy.Builder           as Builder
import qualified Data.Text.Lazy.Encoding          as Text
import qualified Morte.Core                       as Morte
import qualified Morte.Parser                     as Morte
import qualified Morte.Path                       as Morte
import qualified Network.HTTP.Client              as HTTP
import qualified Network.HTTP.Client.TLS          as HTTP
import qualified Filesystem.Path.CurrentOS        as Filesystem

builderToString :: Builder -> String
builderToString = Text.unpack . Builder.toLazyText

-- | An import failed because of a cycle in the import graph
newtype Cycle = Cycle
    { cyclicImport :: Path  -- ^ The offending cyclic import
    }
  deriving (Typeable)

instance Exception Cycle

instance Show Cycle where
    show (Cycle path) = "Cyclic import: " ++ builderToString (build path)

{-| Morte tries to ensure that all expressions hosted on network endpoints are
    weakly referentially transparent, meaning roughly that any two clients will
    compile the exact same result given the same URL.

    To be precise, a strong interpretaton of referential transparency means that
    if you compiled a URL you could replace the expression hosted at that URL
    with the compiled result.  Let's term this \"static linking\".  Morte (very
    intentionally) does not satisfy this stronger interpretation of referential
    transparency since \"statically linking\" an expression (i.e. permanently
    resolving all imports) means that the expression will no longer update if
    its dependencies change.

    In general, either interpretation of referential transparency is not
    enforceable in a networked context since one can easily violate referential
    transparency with a custom DNS, but Morte can still try to guard against
    common unintentional violations.  To do this, Morte enforces that a
    non-local import may not reference a local import.

    Local imports are defined as:

    * A file

    * A URL with a host of @localhost@ or @127.0.0.1@

    All other imports are defined to be non-local
-}
newtype ReferentiallyOpaque = ReferentiallyOpaque
    { opaqueImport :: Path  -- ^ The offending opaque import
    } deriving (Typeable)

instance Exception ReferentiallyOpaque

instance Show ReferentiallyOpaque where
    show (ReferentiallyOpaque path) =
        "Referentially opaque import: " ++ builderToString (build path)

-- | Extend another exception with the current import stack
data Imported e = Imported
    { importStack :: [Path] -- ^ Imports resolved so far, in reverse order
    , nested      :: e      -- ^ The nested exception
    } deriving (Typeable)

instance Exception e => Exception (Imported e)

instance Show e => Show (Imported e) where
    show (Imported paths e) =
            "\n"
        ++  unlines (map (\path -> "⤷ " ++ builderToString (build path)) paths')
        ++  show e
      where
        -- Canonicalize all paths
        paths' = drop 1 (reverse (canonicalizeAll paths))

data Status = Status
    { _stack   :: [Path]
    , _cache   :: Map Path (Expr Text)
    , _manager :: Maybe Manager
    }

canonicalizeAll :: [Path] -> [Path]
canonicalizeAll = map canonicalize . List.tails

stack :: Lens' Status [Path]
stack k s = fmap (\x -> s { _stack = x }) (k (_stack s))

cache :: Lens' Status (Map Path (Expr Text))
cache k s = fmap (\x -> s { _cache = x }) (k (_cache s))

manager :: Lens' Status (Maybe Manager)
manager k s = fmap (\x -> s { _manager = x }) (k (_manager s))

needManager :: StateT Status IO Manager
needManager = do
    x <- zoom manager State.get
    case x of
        Just m  -> return m
        Nothing -> do
            let settings = HTTP.tlsManagerSettings
                    { HTTP.managerResponseTimeout =
                        HTTP.responseTimeoutMicro 1000000
                    }
            m <- liftIO (HTTP.newManager settings)
            zoom manager (State.put (Just m))
            return m

{-| This function computes the current path by taking the last absolute path
    (either an absolute `FilePath` or `URL`) and combining it with all following
    relative paths

    For example, if the file `./foo/bar` imports `./baz`, that will resolve to
    `./foo/baz`.  Relative imports are relative to a file's parent directory.
    This also works for URLs, too.

    This code is full of all sorts of edge cases so it wouldn't surprise me at
    all if you find something broken in here.  Most of the ugliness is due to:

    * Handling paths ending with @/\@@ by stripping the @/\@@ suffix if and only
      if you navigate to any downstream relative paths
    * Removing spurious @.@s and @..@s from the path

    Also, there are way too many `reverse`s in the URL-handling cod  For now I
    don't mind, but if were to really do this correctly we'd store the URLs as
    `Text` for O(1) access to the end of the string.  The only reason we use
    `String` at all is for consistency with the @http-client@ library.
-}
canonicalize :: [Path] -> Path
canonicalize  []                 = File "."
canonicalize (File file0:paths0) =
    if Filesystem.relative file0
    then go          file0 paths0
    else File (clean file0)
  where
    go currPath  []               = File (clean currPath)
    go currPath (URL  url0:_    ) = combine prefix suffix
      where
        prefix = parentURL (removeAtFromURL url0)

        suffix = clean currPath

        -- `clean` will resolve internal @.@/@..@'s in @currPath@, but we still
        -- need to manually handle @.@/@..@'s at the beginning of the path
        combine url path = case Filesystem.stripPrefix ".." path of
            Just path' -> combine url' path'
              where
                url' = parentURL (removeAtFromURL url)
            Nothing    -> case Filesystem.stripPrefix "." path of
                Just path' -> combine url path'
                Nothing    ->
                    -- This `last` is safe because the lexer constrains all
                    -- URLs to be non-empty.  I couldn't find a simple and safe
                    -- equivalent in the `text` API
                    case Text.last url of
                        '/' -> URL (url <>        path')
                        _   -> URL (url <> "/" <> path')
                  where
                    path' = Text.fromStrict (case Filesystem.toText path of
                        Left  txt -> txt
                        Right txt -> txt )
    go currPath (File file:paths) =
        if Filesystem.relative file
        then go          file'  paths
        else File (clean file')
      where
        file' = Filesystem.parent (removeAtFromFile file) </> currPath
canonicalize (URL path:_) = URL path

parentURL :: Text -> Text
parentURL = Text.dropWhileEnd (/= '/')

removeAtFromURL:: Text -> Text
removeAtFromURL url
    | Text.isSuffixOf "/@" url = Text.dropEnd 2 url
    | Text.isSuffixOf "/"  url = Text.dropEnd 1 url
    | otherwise                =                url

removeAtFromFile :: FilePath -> FilePath
removeAtFromFile file =
    if Filesystem.filename file == "@"
    then Filesystem.parent file
    else file

-- | Remove all @.@'s and @..@'s in the path
clean :: FilePath -> FilePath
clean = strip . Filesystem.collapse
  where
    strip p = case Filesystem.stripPrefix "." p of
        Nothing -> p
        Just p' -> p'

{-| Load a `Path` as a \"dynamic\" expression (without resolving any imports)

    This also returns the true final path (i.e. explicit "/@" at the end for
    directories)
-}
loadDynamic :: Path -> StateT Status IO (Expr (EmbedPath Text))
loadDynamic p = do
    paths <- zoom stack State.get

    let readURL url = do
            request <- liftIO (HTTP.parseUrlThrow (Text.unpack url))
            m       <- needManager
            let httpLbs' = do
                    HTTP.httpLbs request m `catch` (\e -> case e of
                        HTTP.HttpExceptionRequest _ (HTTP.StatusCodeException _ _) -> do
                            let request' = request
                                    { HTTP.path = HTTP.path request <> "/@" }
                            -- If the fallback fails, reuse the original
                            -- exception to avoid user confusion
                            HTTP.httpLbs request' m
                                `onException` throwIO (Imported paths e)
                        _ -> throwIO (Imported paths e) )
            response <- liftIO httpLbs'
            case Text.decodeUtf8' (HTTP.responseBody response) of
                Left  err -> liftIO (throwIO (Imported paths err))
                Right txt -> return txt

    let readFile' file = liftIO (do
            (do txt <- Filesystem.readTextFile file
                return (Text.fromStrict txt) ) `catch` (\e -> do
                -- Unfortunately, GHC throws an `InappropriateType`
                -- exception when trying to read a directory, but does not
                -- export the exception, so I must resort to a more
                -- heavy-handed `catch`
                let _ = e :: IOException
                -- If the fallback fails, reuse the original exception to
                -- avoid user confusion
                let file' = file </> "@"
                txt <- Filesystem.readTextFile file'
                    `onException` throwIO (Imported paths e)
                return (Text.fromStrict txt) ) )

    txt <- case canonicalize (p:paths) of
        File file -> readFile' file
        URL  url  -> readURL   url

    let abort err = liftIO (throwIO (Imported (p:paths) err))
    case Morte.exprFromText txt of
        Left  err  -> case canonicalize (p:paths) of
            URL url -> do
                -- Also try the fallback in case of a parse error, since the
                -- parse error might signify that this URL points to a directory
                -- list
                request  <- liftIO (HTTP.parseUrlThrow (Text.unpack url))
                let request' = request { HTTP.path = HTTP.path request <> "/@" }
                m        <- needManager
                response <- liftIO
                    (HTTP.httpLbs request' m `onException` abort err)
                case Text.decodeUtf8' (HTTP.responseBody response) of
                    Left  _    -> liftIO (abort err)
                    Right txt' -> case Morte.exprFromText txt' of
                        Left  _    -> liftIO (abort err)
                        Right expr -> return expr
            _       -> liftIO (abort err)
        Right expr -> return expr

resolvePaths :: Expr (EmbedPath Text) -> StateT Status IO (Expr Text)
resolvePaths = fmap join . traverse unEmbed
  where
    unEmbed emb = case emb of
        Morte.V var  -> return (Morte.Var var)
        Morte.P path -> loadStatic path

asFullyResolved :: Expr (EmbedPath Text) -> Maybe (Expr Text)
asFullyResolved = fmap join . traverse filterVars
  where
    filterVars emb = case emb of
        Morte.V var -> Just (Morte.Var var)
        Morte.P _   -> Nothing

-- | Load a `Path` as a \"static\" expression (with all imports resolved)
loadStatic :: Path -> StateT Status IO (Expr Text)
loadStatic path = do
    paths <- zoom stack State.get

    let local (URL url) = case HTTP.parseUrlThrow (Text.unpack url) of
            Nothing      -> False
            Just request -> case HTTP.host request of
                "127.0.0.1" -> True
                "localhost" -> True
                _           -> False
        local (File _)  = True

    let parent = canonicalize paths
    let here   = canonicalize (path:paths)

    if local here && not (local parent)
        then liftIO (throwIO (Imported paths (ReferentiallyOpaque path)))
        else return ()


    (expr, cached) <- if here `elem` canonicalizeAll paths
        then liftIO (throwIO (Imported paths (Cycle path)))
        else do
            m <- zoom cache State.get
            case Map.lookup here m of
                Just expr -> return (expr, True)
                Nothing   -> do
                    expr'  <- loadDynamic path
                    expr'' <- case traverse (\_ -> Nothing) expr' of
                        -- No imports left
                        Just expr -> do
                            zoom cache (State.put $! Map.insert here expr m)
                            return expr
                        -- Some imports left, so recurse
                        Nothing   -> do
                            let paths' = path:paths
                            zoom stack (State.put paths')
                            expr'' <- resolvePaths expr'
                            zoom stack (State.put paths)
                            return expr''
                    return (expr'', False)

    -- Type-check expressions here for two separate reasons:
    --
    --  * to verify that they are closed
    --  * to catch type errors as early in the import process as possible
    --
    -- There is no need to check expressions that have been cached, since they
    -- have already been checked
    if cached
        then return ()
        else case Morte.typeOf expr of
            Left  err -> liftIO (throwIO (Imported (path:paths) err))
            Right _   -> return ()

    return expr

{-| Resolve all imports within an expression

    By default the starting path is the current directory, but you can override
    the starting path with a file if you read in the expression from that file
-}
load
    :: Maybe Path
    -- ^ Starting path
    -> Expr (EmbedPath Text)
    -- ^ Expression to resolve
    -> IO (Expr Text)
load here expr =
    State.evalStateT (resolvePaths expr) status
  where
    status = Status (Foldable.toList here) Map.empty Nothing
