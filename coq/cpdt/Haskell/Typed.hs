{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}



module  Haskell.Typed 
    (   Exp     (..)
    ,   Binop   (..)
    ,   Type    (..)
    ,   TypeDenote
    ,   eval
    )   where

data Type = Natural | Boolean

data Binop a b c where
    Plus  :: Binop Natural Natural Natural
    Times :: Binop Natural Natural Natural
    EqN   :: Binop Natural Natural Boolean 
    EqB   :: Binop Boolean Boolean Boolean 
    Lt    :: Binop Natural Natural Boolean

data Exp a where
    NConst :: Integer -> Exp Natural
    BConst :: Bool    -> Exp Boolean
    Binop  :: Binop a b c -> Exp a -> Exp b -> Exp c


type family TypeDenote a where
    TypeDenote Natural = Integer
    TypeDenote Boolean = Bool

binopDenote :: Binop a b c -> TypeDenote a -> TypeDenote b -> TypeDenote c
binopDenote Plus  = (+)
binopDenote Times = (*)
binopDenote EqN   = (==)
binopDenote EqB   = (==)
binopDenote Lt    = (<)

expDenote :: Exp a -> TypeDenote a
expDenote (NConst n) = n
expDenote (BConst b) = b
expDenote (Binop b e1 e2) = binopDenote b (expDenote e1) (expDenote e2)


data TStack = SNil | SCons Type TStack

type (:::) = SCons

infixr 5 :::

data Instr a b where
    INConst :: Integer     -> Instr s (Natural ::: s)
    IBConst :: Bool        -> Instr s (Boolean ::: s)
    IBinop  :: Binop a b c -> Instr (a ::: b ::: s) (c ::: s)
    
data Prog a b where
    PNil  :: Prog s s 
    PCons :: Instr s1 s2 -> Prog s2 s3 -> Prog s1 s3

type family VStack a where
    VStack SNil = ()
    VStack (a ::: as) = (TypeDenote a, VStack as)

instrDenote :: Instr a b -> VStack a -> VStack b
instrDenote (INConst n) v = (n,v)
instrDenote (IBConst b) v = (b,v)
instrDenote (IBinop b) (v1, (v2, v)) = (binopDenote b v1 v2, v)


progDenote :: Prog a b -> VStack a -> VStack b
progDenote PNil v        = v
progDenote (PCons i p) v = progDenote p $ instrDenote i v

append :: Prog a b -> Prog b c -> Prog a c
append PNil q         = q
append (PCons i p) q  = PCons i (append p q)


compile_ :: Exp t -> Prog s (t ::: s)
compile_ (NConst n) = PCons (INConst n) PNil 
compile_ (BConst b) = PCons (IBConst b) PNil
compile_ (Binop b e1 e2) = append (compile_ e2) $ 
    append (compile_ e1) (PCons (IBinop b) PNil)

compile :: Exp t -> Prog SNil (t ::: SNil)
compile = compile_

eval :: Exp t -> TypeDenote t
eval e = let (v,()) = progDenote (compile e) () in v 



