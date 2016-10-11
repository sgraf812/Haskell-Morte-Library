{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | All `Context`-related operations

module Morte.Context (
    -- * Context
      Context
    , empty
    , insert
    , lookup
    , toList
    ) where

import           Control.DeepSeq (NFData)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Text.Lazy  (Text)
import           Prelude         hiding (lookup)

{-| Bound variable names and their types

    Variable names may appear more than once in the `Context`.  The `Var` @x\@n@
    refers to the @n@th occurrence of @x@ in the `Context` (using 0-based
    numbering).
-}
newtype Context a = Context { getContext :: Map Text a }
    deriving (Functor, NFData, Eq, Ord, Show, Read)

{-| An empty context with no key-value pairs

> toList empty = []
-}
empty :: Context a
empty = Context Map.empty

-- | Add a key-value pair to the `Context`
insert :: Text -> a -> Context a -> Context a
insert k v (Context kvs) = Context (Map.insert k v kvs)
{-# INLINABLE insert #-}

{-| Lookup a key by name and index

> lookup k 0 (insert k v0              ctx ) = Just v0
> lookup k 1 (insert k v0 (insert k v1 ctx)) = Just v1
-}
lookup :: Text -> Context a -> Maybe a
lookup k (Context kvs) = Map.lookup k kvs
{-# INLINABLE lookup #-}

-- | Return all key-value associations as a list
toList :: Context a -> [(Text, a)]
toList = Map.toList . getContext
{-# INLINABLE toList #-}
