{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE UndecidableInstances       #-}

import Data.Maybe

-- 'thunk' is a type of thunk which can be evaluated to an 'a'
class Eval thunk a | thunk -> a where
    eval :: thunk -> a

-- A type of thunk which returns an 'a'
data Fst a b = Fst (a,b)

instance Eval (Fst a b) a where
    eval (Fst x) = fst x

data Snd a b = Snd (a,b)
instance Eval (Snd a b) b where
    eval (Snd x) = snd x

data ListToMaybe a = ListToMaybe [a]

instance Eval (ListToMaybe a) (Maybe a) where
    eval (ListToMaybe x) = listToMaybe x

data MapList a b = MapList (a -> b) [a]
instance Eval (MapList a b) [b] where
    eval (MapList f xs) = map f xs

data MapList' a thunk = MapList' (a -> thunk) [a]
instance (Eval thunk b) => Eval (MapList' a thunk) [b] where
    eval (MapList' f xs) = map (eval . f) xs

main :: IO ()
main = do
    print $ eval $ Fst ("hello", True)
    print $ eval $ ListToMaybe ([] :: [Int])
    print $ eval $ ListToMaybe ["a","b","c"]
    print $ eval $ MapList  fst [("hello",1 :: Int),("world",2)]
    print $ eval $ MapList' Fst [("hello",1 :: Int),("world",2)]


