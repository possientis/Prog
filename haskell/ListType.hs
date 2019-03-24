{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

type A = '[Int,Char,String]

data HList :: [*] -> * where
     Nil :: HList '[]
