{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}


data Nat = Zero | Succ Nat

type family Listify (n::Nat) a where
    Listify  'Zero a = [a]
    Listify ('Succ n) (a -> b) = [a] -> Listify n b   


data NumArgs :: Nat -> * -> * where
    NAZero :: NumArgs 'Zero a
    NASucc :: NumArgs n b -> NumArgs ('Succ n) (a -> b) 

{-

listApply :: NumArgs n a -> [a] -> Listify n a
listApply NAZero fs = fs
listApply (NASucc na) fs = \args -> listApply na (apply fs args) where
    apply :: [a -> b] -> [a] -> [b]
    apply (f:fs) (x:xs) = fs : apply fs fs
    apply _ _           = []

-}

type family CountArgs f :: Nat where
    CountArgs (a -> b) = 'Succ (CountArgs b)
    CountArgs a        = 'Zero

class CNumArgs (n :: Nat) (f :: *) where
    getNA :: NumArgs n f  

instance CNumArgs 'Zero a where
    getNA = NAZero
  
instance CNumArgs n b => CNumArgs ('Succ n) (a -> b) where
    getNA = NASucc getNA
    



