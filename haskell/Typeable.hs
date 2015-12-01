class Typeable a where
  typeRep :: a -> TypeRep
  proxy :: a

data TypeRep = TR String [TypeRep] deriving Show

instance Typeable Int where
  typeRep _ = TR "Int" []
  proxy = 0::Int
-- doesnt work :(
instance Typeable a => Typeable [a] where
  typeRep _ = TR "List" [typeRep (proxy::a)]
