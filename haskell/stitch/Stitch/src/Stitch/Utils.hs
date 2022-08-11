module Stitch.Utils
  ( Precedence 
  , maybeParens
  , topPrec
  ) where

--import Text.Parsec
import Text.PrettyPrint.ANSI.Leijen 

type Precedence = Rational

topPrec :: Precedence
topPrec = 0

-- | Enclose a 'Doc' in parens if the flag is 'True'
maybeParens :: Bool -> Doc -> Doc
maybeParens True  = parens
maybeParens False = id 
