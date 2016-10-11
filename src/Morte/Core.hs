{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}

{-| This module contains the core calculus for the Morte language.  This
    language is a minimalist implementation of the calculus of constructions,
    which is in turn a specific kind of pure type system.  If you are new to
    pure type systems you may wish to read \"Henk: a typed intermediate
    language\".

    <http://research.microsoft.com/en-us/um/people/simonpj/papers/henk.ps.gz>


    Morte is a strongly normalizing language, meaning that:

    * Every expression has a unique normal form computed by `normalize`

    * You test expressions for equality of their normal forms using `==`

    * Equational reasoning preserves normal forms


    Strong normalization comes at a price: Morte forbids recursion.  Instead,
    you must translate all recursion to F-algebras and translate all corecursion
    to F-coalgebras.  If you are new to F-(co)algebras then you may wish to read
    "Morte.Tutorial" or read \"Recursive types for free!\":

    <http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt>

    Morte is designed to be a super-optimizing intermediate language with a
    simple optimization scheme.  You optimize a Morte expression by just
    normalizing the expression.  If you normalize a long-lived program encoded
    as an F-coalgebra you typically get a state machine, and if you normalize a
    long-lived program encoded as an F-algebra you typically get an unrolled
    loop.

    Strong normalization guarantees that all abstractions encodable in Morte are
    \"free\", meaning that they may increase your program's compile times but
    they will never increase your program's run time because they will normalize
    to the same code.
-}

module Morte.Core (
    -- * Syntax
    Var(..),
    Const(..),
    Path(..),
    X(..),
    Expr(..),
    Context,

    -- * Core functions
    typeWith,
    typeWith,
    normalize,

    -- * Utilities
    shift,
    subst,
    pretty,

    -- * Errors
    TypeError(..),
    TypeMessage(..),
    ) where

import           Bound                            (Scope (..), Var (..), (>>>=))
import qualified Bound
import           Bound.Name                       (Name (..), name)
#if MIN_VERSION_base(4,8,0)
#else
import           Control.Applicative              (Applicative (..), (<$>))
#endif
import           Control.DeepSeq                  (NFData (..))
import           Control.Error.Util               (note)
import           Control.Exception                (Exception)
import           Control.Monad                    (ap, join, mzero)
import           Data.Binary                      (Binary (..), Get, Put)
import           Data.Coerce
import           Data.Foldable
import           Data.Maybe                       (isNothing)
import           Data.Monoid                      ((<>))
import           Data.String                      (IsString (..))
import           Data.Text.Buildable              (Buildable (..))
import           Data.Text.Lazy                   (Text)
import           Data.Text.Lazy.Builder           (Builder)
import           Data.Traversable
import           Data.Typeable                    (Typeable)
import           Data.Word                        (Word8)
import           Filesystem.Path.CurrentOS        (FilePath)
import           Prelude                          hiding (FilePath)
#if MIN_VERSION_transformers(0,5,0) || !MIN_VERSION_transformers(0,4,0)
import           Data.Deriving                    (deriveEq1, deriveOrd1,
                                                   deriveRead1, deriveShow1)
import           Data.Functor.Classes
#else
import           Prelude.Extras
#endif

import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Binary.Get                  as Get
import qualified Data.Binary.Put                  as Put
import qualified Data.Text.Encoding               as Text
import qualified Data.Text.Lazy                   as Text
import qualified Data.Text.Lazy.Builder           as Builder
import qualified Filesystem.Path.CurrentOS        as Filesystem
import           GHC.Generics                     (Generic)

{-| Label for a bound variable

    The `Text` field is the variable's name (i.e. \"@x@\").

    The `Int` field disambiguates variables with the same name if there are
    multiple bound variables of the same name in scope.  Zero refers to the
    nearest bound variable and the index increases by one for each bound variable
    of the same name going outward.  The following diagram may help:

>                           +-refers to-+
>                           |           |
>                           v           |
> \(x : *) -> \(y : *) -> \(x : *) -> x@0
>
>   +-------------refers to-------------+
>   |                                   |
>   v                                   |
> \(x : *) -> \(y : *) -> \(x : *) -> x@1

    This `Int` behaves like a De Bruijn index in the special case where all
    variables have the same name.

    You can optionally omit the index if it is @0@:

>                           +refers to+
>                           |         |
>                           v         |
> \(x : *) -> \(y : *) -> \(x : *) -> x

    Zero indices are omitted when pretty-printing `Var`s and non-zero indices
    appear as a numeric suffix.
-}
-- data Var = V Text Int deriving (Eq, Show)

putUtf8 :: Text -> Put
putUtf8 txt = put (Text.encodeUtf8 (Text.toStrict txt))

getUtf8 :: Get Text
getUtf8 = do
    bs <- get
    case Text.decodeUtf8' bs of
        Left  e   -> fail (show e)
        Right txt -> return (Text.fromStrict txt)

{-| Constants for the calculus of constructions

    The only axiom is:

> ⊦ * : □

    ... and all four rule pairs are valid:

> ⊦ * ↝ * : *
> ⊦ □ ↝ * : *
> ⊦ * ↝ □ : □
> ⊦ □ ↝ □ : □

-}
data Const = Star | Box deriving (Eq, Ord, Show, Read, Bounded, Enum)

instance Binary Const where
    put c = case c of
        Star -> put (0 :: Word8)
        Box  -> put (1 :: Word8)
    get = do
        n <- get :: Get Word8
        case n of
            0 -> return Star
            1 -> return Box
            _ -> fail "get Const: Invalid tag byte"

instance NFData Const where
    rnf c = seq c ()

instance Buildable Const where
    build c = case c of
        Star -> "*"
        Box  -> "□"

axiom :: Const -> Either TypeError Const
axiom Star = return Box
axiom Box  = Left (Untyped Box)

rule :: Const -> Const -> Either TypeError Const
rule Star Box  = return Box
rule Star Star = return Star
rule Box  Box  = return Box
rule Box  Star = return Star

-- | Path to an external resource
data Path
    = File FilePath
    | URL  Text
    deriving (Eq, Ord, Show)

instance Buildable Path where
    build (File file)
        |  Text.isPrefixOf  "./" txt
        || Text.isPrefixOf   "/" txt
        || Text.isPrefixOf "../" txt
        = build txt <> " "
        | otherwise
        = "./" <> build txt <> " "
      where
        txt = Text.fromStrict (either id id (Filesystem.toText file))
    build (URL  str ) = build str <> " "

{-| Like `Data.Void.Void`, except with an `NFData` instance in order to avoid
    orphan instances
-}
newtype X = X { absurd :: forall a . a }

instance Eq X where
    _ == _ = True

instance Show X where
    show = absurd

instance NFData X where
    rnf x = seq x ()

instance Buildable X where
    build = absurd

instance Binary X where
    get = mzero
    put = absurd

-- | Syntax tree for expressions
data Expr var
    -- | > Const c        ~  c
    = Const Const
    -- | > Var (V x 0)    ~  x
    --   > Var (V x n)    ~  x@n
    | Var var
    -- | > Lam x     A b  ~  λ(x : A) → b
    | Lam (Name Text ()) (Type var) (Scope () Expr var)
    -- | > Pi x      A B  ~  ∀(x : A) → B
    --   > Pi unused A B  ~        A  → B
    | Pi  (Name Text ()) (Type var) (Scope () Expr var)
    -- | > App f a        ~  f a
    | App (Expr var) (Expr var)
    deriving (Eq, Ord, Functor, Foldable, Traversable, Show, Read, Generic)

type Type = Expr

type ClosedExpr = Expr X

-- higher-rank Eq*, Ord*, Show*, Read* are needed because of polymorphic
-- recursion in @Scope@. The respective classes moved from transformers
-- to Data.Functor.Classes, so beginning with transformers-0.5 we use them.
-- Unfortunately, we can't derive the instances at the moment.
-- Fortunately, there's deriving-compat.
#if MIN_VERSION_transformers(0,5,0) || !MIN_VERSION_transformers(0,4,0)
$(deriveEq1 ''Expr)
$(deriveOrd1 ''Expr)
$(deriveShow1 ''Expr)
$(deriveRead1 ''Expr)
#else
instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr
instance Read1 Expr
#endif

instance Applicative Expr where
    pure = Var
    (<*>) = ap

instance Monad Expr where
    return = pure
    Const c     >>= _ = Const c
    Var x       >>= f = f x
    Lam x _A  b >>= f = Lam x (_A >>= f) (b >>>= f)
    Pi  x _A _B >>= f = Pi  x (_A >>= f) (_B >>>= f)
    App g a     >>= f = App (g >>= f) (a >>= f)


instance Binary (Expr Text) where
    put e = case e of
        Const c     -> do
            put (0 :: Word8)
            put c
        Var x       -> do
            put (1 :: Word8)
            put x
        Lam (Name x _) _A b  -> do
            put (2 :: Word8)
            put x
            put _A
            put (Bound.instantiate1 (pure x) b)
        Pi  (Name x _) _A _B -> do
            put (3 :: Word8)
            put x
            put _A
            put (Bound.instantiate1 (pure x) _B)
        App f a     -> do
            put (4 :: Word8)
            put f
            put a

    get = do
        n <- get :: Get Word8
        case n of
            0 -> Const <$> get
            1 -> Var <$> get
            2 -> do
                x <- get
                _A <- get
                b <- Bound.abstract1 (name x) <$> get
                return (Lam x _A b)
            3 -> do
                x <- get
                _A <- get
                _B <- Bound.abstract1 (name x) <$> get
                return (Pi x _A _B)
            4 -> App <$> get <*> get
            _ -> fail "get Expr: Invalid tag byte"

instance IsString var => IsString (Expr var) where
    fromString str = Var (fromString str)

instance (NFData b, NFData a) => NFData (Var b a)
instance (NFData b, NFData a) => NFData (Name b a)

instance (NFData (f (Var b (f a))), NFData (f a)) => NFData (Scope b f a) where
    rnf (Scope s) = rnf s

instance NFData var => NFData (Expr var) where
    rnf e = case e of
        Const c     -> rnf c
        Var   v     -> rnf v
        Lam x _A b  -> rnf x `seq` rnf _A `seq` rnf b
        Pi  x _A _B -> rnf x `seq` rnf _A `seq` rnf _B
        App f a     -> rnf f `seq` rnf a

-- | Generates a syntactically valid Morte program
instance Buildable var => Buildable (Expr var)
  where
    build = go False False . fmap build
      where
        paren False s = s
        paren True  s = "(" <> s <> ")"

        go :: Bool -> Bool -> Expr Builder -> Builder
        go parenBind parenApp e = case e of
            Const c              -> build c
            Var x                -> x
            Lam (Name x _) _A b  -> paren parenBind $
                    "λ("
                <>  build x
                <>  " : "
                <>  go False False _A
                <>  ") → "
                <>  go False False (Bound.instantiate1 (pure (build x)) b)
            Pi  (Name x _) _A _B -> paren parenBind $
                    (if x /= "_"
                     then "∀(" <> build x <> " : " <> go False False _A <> ")"
                     else go True False _A )
                <>  " → "
                <>  go False False (Bound.instantiate1 (pure (build x)) _B)
            App f a              -> go True False f <> " " <> go True True a

-- | The specific type error
data TypeError
    = UnboundVariable Builder
    | InvalidInputType (Expr Builder) (Type Builder)
    | InvalidOutputType (Expr Builder) (Type Builder)
    | NotAFunction (Expr Builder) (Type Builder)
    | TypeMismatch (Expr Builder) (Type Builder) (Type Builder)
    | Untyped Const
    deriving (Show, Generic)

instance NFData TypeError

instance Buildable TypeError where
    build msg = case msg of
        UnboundVariable x        ->
                "\n"
            <>  "\n"
            <>  "Error: Unbound variable\n"
            <>  "Variable: " <> x <> "\n"
        InvalidInputType expr ty  ->
                "Error: Invalid input type\n"
            <>  "\n"
            <>  buildExpr expr
            <>  buildType ty
        InvalidOutputType expr ty ->
                "Error: Invalid output type\n"
            <>  "\n"
            <>  buildExpr expr
            <>  buildType ty
        NotAFunction e f          ->
                "Error: Only functions may be applied to values\n"
            <>  "\n"
            <>  buildExpr e
            <>  buildType f
        TypeMismatch e exp arg    ->
                "Error: Function applied to argument of the wrong type\n"
            <>  "\n"
            <>  buildExpr e
            <>  "Expected type: " <> build exp <> "\n"
            <>  "Argument type: " <> build arg <> "\n"
        Untyped c                 ->
                "Error: " <> build c <> " has no type\n"
      where
        buildExpr e = "Expression: " <> build e <> "\n"
        buildType ty = "Type: " <> build ty <> "\n"

instance Exception TypeError

type CheckResult var = Either TypeError var

type Context var = var -> CheckResult (Type var)

consContext :: (Expr var) -> Context var -> Context (Var () var)
consContext v ctx k = case k of
    B () -> pure (F <$> v)
    F k  -> (F <$>) <$> ctx k

asConst :: Expr var -> Maybe Const
asConst e = case e of
    Const c -> Just c
    _       -> Nothing

asPi :: Expr var -> Maybe (Type var, Scope () Type var)
asPi e = case e of
    Pi _ _A _B -> Just (_A, _B)
    _          -> Nothing

{-| Type-check an expression and return the expression's type if type-checking
    suceeds or an error if type-checking fails

    `typeWith` does not necessarily normalize the type since full normalization
    is not necessary for just type-checking.  If you actually care about the
    returned type then you may want to `normalize` it afterwards.
-}
typeWith :: (Eq var, Buildable var) => Context var -> Expr var -> CheckResult (Type var)
typeWith ctx e = case e of
    Const c     -> fmap Const (axiom c)
    Var v -> ctx v
    Lam x _A b  -> do
        -- TODO: Maybe use let _A' = whnf _A instead of _A?
        --       Depends on whether _A will be reduced anyway
        --       during checking and quality of error messages
        _B <- fmap Bound.toScope (typeWith (consContext _A ctx) (Bound.fromScope b))
        let p = Pi x _A _B
        _t <- typeWith ctx p
        return p
    Pi  ~(Name x _) _A _B -> do
        eS <- typeWith ctx _A
        let errInp = InvalidInputType (fmap build e) (fmap build _A)
        s  <- (note errInp . asConst . whnf) eS
        eT <- typeWith (consContext _A ctx) (Bound.fromScope _B)
        let errOut = InvalidOutputType (fmap build e) (Bound.instantiate1 (pure (build x)) (fmap build _B))
        t  <- (note errOut . asConst . whnf) eT
        fmap Const (rule s t)
    App f a     -> do
        _F       <- typeWith ctx f
        let err = NotAFunction (fmap build e) (fmap build _F)
        (_A, _B) <- (note err . asPi . whnf) _F
        _A'      <- typeWith ctx a
        let nf_A  = normalize _A
            nf_A' = normalize _A'
        if nf_A == nf_A'
            then return (Bound.instantiate1 a _B)
            else Left (TypeMismatch (fmap build e) (fmap build nf_A) (fmap build nf_A'))

noFreeVars :: Buildable var => Context var
noFreeVars x = Left (UnboundVariable (build x))

{-| `typeOf` is the same as `typeWith` with an empty context, meaning that the
    expression must be closed (i.e. no free variables), otherwise type-checking
    will fail.
-}
typeOf :: (Eq var, Buildable var) => Expr var -> CheckResult (Type var)
typeOf = typeWith noFreeVars

-- | Reduce an expression to weak-head normal form
whnf :: Expr var -> Expr var
whnf e = case e of
    App f a -> case whnf f of
        Lam x _A b -> whnf (Bound.instantiate1 a b)  -- Beta reduce
        f'         -> App f' a
    _       -> e

-- | Try to unshift the given expression if its argument is unused.
tryUnshift :: Monad f => Scope b f a -> Maybe (f a)
tryUnshift = traverse unF . Bound.fromScope
  where
    unF x = case x of
        F e -> Just e
        _ -> Nothing

{-| Reduce an expression to its normal form, performing both beta reduction and
    eta reduction

    `normalize` does not type-check the expression.  You may want to type-check
    expressions before normalizing them since normalization can convert an
    ill-typed expression into a well-typed expression.
-}
normalize :: Expr var -> Expr var
normalize e = case e of
    Lam x _A (Scope b)  -> case b' of
        App f (Var (B ())) -> case tryUnshift f of
            Just f' -> f'
            _       -> e'
        _       -> e'
      where
        b' = normalize b
        e' = Lam x (normalize _A) (Scope b')
    Pi  x _A (Scope _B) -> Pi x (normalize _A) (Scope (normalize _B))
    App f a             -> case normalize f of
        Lam x _A b -> normalize (Bound.instantiate1 (normalize a) (normalize b))  -- Beta reduce
        f'         -> App f' (normalize a)
    _                   -> e

-- | Pretty-print a value
pretty :: Buildable a => a -> Text
pretty = Builder.toLazyText . build
