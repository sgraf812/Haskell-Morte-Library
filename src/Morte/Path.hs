{-# LANGUAGE OverloadedStrings  #-}

module Morte.Path (
      Path(..)
    , EmbedPath(..)
    ) where

import Data.Monoid ((<>))
import Data.Text.Buildable (Buildable(..))
import Data.Text.Lazy (Text)
import Filesystem.Path ((</>), FilePath)
import qualified Filesystem.Path.CurrentOS        as Filesystem
import Prelude hiding (FilePath)

import qualified Data.Text.Lazy as Text

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

data EmbedPath var
    = P Path
    | V var
    deriving (Eq, Ord, Show)

instance Buildable var => Buildable (EmbedPath var) where
    build (P path) = build path
    build (V var) = build var
