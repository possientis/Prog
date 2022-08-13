{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ExplicitForAll     #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE TypeFamilies       #-}
{-# OPTIONS_GHC -Wno-orphans    #-}

module Stitch.Utils
  ( Precedence 
  , ($$)
  , allPairs
  , foldl1M
  , maybeParens
  , minus
  , render
  , stripWhitespace
  , topPrec
  , toSimpleDoc
  ) where

import Control.Monad
import Data.Char
import Data.List
import Text.Parsec
import Text.PrettyPrint.ANSI.Leijen   as Pretty

import Stitch.Data.Fin
import Stitch.Data.Singletons
import Stitch.Data.Nat

instance Pretty ParseError where
  pretty = text . show

-- | A better synonym for operator precedence
type Precedence = Rational

-- | Precedence for top-level printing
topPrec :: Precedence
topPrec = 0

-- | Convert a 'Doc' to a 'String'
render :: Doc -> String
render = flip displayS "" . toSimpleDoc

-- | Convert a 'Doc' to a 'SimpleDoc' for further rendering
toSimpleDoc :: Doc -> SimpleDoc
toSimpleDoc = renderPretty 1.0 78

-- | Enclose a 'Doc' in parens if the flag is 'True'
maybeParens :: Bool -> Doc -> Doc
maybeParens True  = parens
maybeParens False = id 

-- | Synonym for 'Pretty.<$>'
($$) :: Doc -> Doc -> Doc
($$) = (Pretty.<$>)

-- | (Inefficiently) strips whitespace from a string
stripWhitespace :: String -> String
stripWhitespace = dropWhile isSpace . dropWhileEnd isSpace

-- | Like 'foldl1', but for a monadic computation
foldl1M :: MonadPlus m => (a -> a -> m a) -> [a] -> m a
foldl1M f (x : xs) = foldM f x xs
foldl1M _ _        = mzero

-- | Compute all pairs from the elements in a list; the
-- first element of the pair always occurs before the second
-- in the original list.
allPairs :: [a] -> [(a,a)]
allPairs []     = []
allPairs [_]    = []
allPairs (x:xs) = map (x,) xs ++ allPairs xs

-- | Substract two Nat's safely
minus :: forall (n :: Nat) . Sing n -> Fin n -> Nat
minus (SSucc n) (FS v) = n `minus` v
minus n          FZ    = fromSing n
