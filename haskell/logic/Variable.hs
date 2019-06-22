{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE FlexibleInstances  #-}

module  Variable
    (   Var
    ,   a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z
    ,   main
    )   where

import GHC.Generics
import Test.QuickCheck

main :: IO ()
main = do
    sample (arbitrary :: Gen (Var -> Var))

mainVars ::[Var]
mainVars = [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z]

newtype Var = Var { unVar :: Integer}
    deriving (Eq,Ord,Generic)

instance Show Var where
    show vv
        | vv == a   = "a"
        | vv == b   = "b"
        | vv == c   = "c"
        | vv == d   = "d"
        | vv == e   = "e"
        | vv == f   = "f"
        | vv == g   = "g"
        | vv == h   = "h"
        | vv == i   = "i"
        | vv == j   = "j"
        | vv == k   = "k"
        | vv == l   = "l"
        | vv == m   = "m"
        | vv == n   = "n"
        | vv == o   = "o"
        | vv == p   = "p"
        | vv == q   = "q"
        | vv == r   = "r"
        | vv == s   = "s"
        | vv == t   = "t"
        | vv == u   = "u"
        | vv == v   = "v"
        | vv == w   = "w"
        | vv == x   = "x"
        | vv == y   = "y"
        | vv == z   = "z"
        | otherwise = "x" ++ (show $ unVar vv)

instance Arbitrary Var where
    arbitrary = do
        num <- elements [20..25] :: Gen Integer
        return $ Var num

instance CoArbitrary Var where
    coarbitrary = genericCoarbitrary

toList :: (Var -> Var) -> [(Var,Var)]
toList fun = map (\var -> (var, fun var)) mainVars

instance Show (Var -> Var) where
    show = show . toList

a :: Var
b :: Var 
c :: Var 
d :: Var 
e :: Var
f :: Var
g :: Var
h :: Var
i :: Var
j :: Var
k :: Var
l :: Var
m :: Var
n :: Var
o :: Var
p :: Var
q :: Var
r :: Var
s :: Var
t :: Var
u :: Var 
v :: Var
w :: Var
x :: Var 
y :: Var 
z :: Var 

a = Var 0
b = Var 1
c = Var 2 
d = Var 3 
e = Var 4
f = Var 5
g = Var 6
h = Var 7
i = Var 8
j = Var 9
k = Var 10
l = Var 11
m = Var 12
n = Var 13
o = Var 14
p = Var 15
q = Var 16
r = Var 17
s = Var 18
t = Var 19
u = Var 20
v = Var 21
w = Var 22
x = Var 23 
y = Var 24
z = Var 25 
