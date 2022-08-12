module Stitch.Parse
  (
  ) where

--import Text.Parsec.Prim

----------------------
-- Plumbing

-- A parser usable in a context with n bound variables
-- the "state" is a list of bound names. searching a bound name in the list
-- gives you the correct deBruijn index
--type Parser n a = ParsecT [LToken] () (Reader (Vec n String)) a


