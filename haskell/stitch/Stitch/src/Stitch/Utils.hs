{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ExplicitForAll     #-}
{-# LANGUAGE TypeFamilies       #-}

module Stitch.Utils
  ( Precedence 
  , maybeParens
  , minus
  , render
  , topPrec
  ) where

--import Text.Parsec
import Text.PrettyPrint.ANSI.Leijen 

import Stitch.Data.Fin
import Stitch.Data.Singletons
import Stitch.Data.Nat

type Precedence = Rational

topPrec :: Precedence
topPrec = 0

-- | Enclose a 'Doc' in parens if the flag is 'True'
maybeParens :: Bool -> Doc -> Doc
maybeParens True  = parens
maybeParens False = id 

-- | Convert a 'Doc' to a 'String'
render :: Doc -> String
render = flip displayS "" . toSimpleDoc

-- | Convert a 'Doc' to a 'SimpleDoc' for further rendering
toSimpleDoc :: Doc -> SimpleDoc
toSimpleDoc = renderPretty 1.0 78

-- | Substract two Nat's safely
minus :: forall (n :: Nat) . Sing n -> Fin n -> Nat
minus (SSucc n) (FS v) = n `minus` v
minus n          FZ    = fromSing n



