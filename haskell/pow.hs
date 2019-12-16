{-# LANGUAGE GADTs              #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE KindSignatures     #-}

data Nat = Z | S Nat

type family Pow (a :: *) (n :: Nat) :: * where
    Pow a  'Z    = ()
    Pow a ('S n) = (a, Pow a n)

type family Log (p :: *) :: Nat where
    Log ()    = 'Z
    Log (_,b) = 'S (Log b) 


type T1 = 'S ('S ('S 'Z))
type T2 = Pow Int T1
type T3 = Log T2




