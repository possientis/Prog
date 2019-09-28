{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE UndecidableInstances       #-}

class Eval func a | func -> a where
    eval :: func -> a

data Fst a b = Fst (a,b)
instance Eval (Fst a b) a where
    eval (Fst (a,_)) = a

data ListToMaybe a = ListToMaybe [a]
instance Eval (ListToMaybe a) (Maybe a) where
    eval (ListToMaybe [])       = Nothing
    eval (ListToMaybe (x:_))    = Just x

data MapList func a = MapList (a -> func) [a]
instance (Eval func b) => Eval (MapList func a) [b] where
    eval (MapList _ []) = []
    eval (MapList f (a:as)) = eval (f a) : eval (MapList f as)


 
main :: IO ()
main = do
    print $ eval $ Fst ("hello", True)
    print $ eval $ ListToMaybe ([] :: [Int])
    print $ eval $ ListToMaybe ["a","b","c"]
    print $ eval $ MapList Fst [("hello",1 :: Int),("world",2)]


