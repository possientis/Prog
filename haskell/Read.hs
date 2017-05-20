import Text.Read

infixr 5 :^:
data Tree a = Leaf a | Tree a :^: Tree a

{-
class Read a where
  readsPrec :: Int -> ReadS a
  readList :: ReadS [a]
  readPrec :: ReadPrec a
  readListPrec :: ReadPrec [a]
-}

-- parens :: ReadPrec a -> ReadPrec a


instance (Read a) => Read (Tree a) where
  readPrec = undefined
