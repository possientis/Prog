{-# LANGUAGE GADTs              #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE ExplicitForAll     #-}

module  Formula
    (   (:->:)
    ,   (:&&:)
    ,   (:::)
    ,   (:=>:)  (..)
    ,   Formula (..)
    ,   Context (..)
    ,   T
    ,   C1
    ,   C2
    ,   lemma1
    ,   lemma2
    ,   lemma3
    ,   deduction
    ,   and1
    ,   and2
    ,   and3
    )   where

import GHC.TypeLits

data Formula
    = Var Nat
    | Top
    | Imp Formula Formula
    | And Formula Formula

data Context 
    = Nil
    | Cons Formula Context

infixr 3 :->:
infixr 4 :&&:
infixr 2 :::
infix  1 :=>:

type (:->:) = 'Imp
type (:&&:) = 'And
type T      = 'Top
type V      = 'Var
type (:::)  = 'Cons
type O      = 'Nil 

type P1 =  V 2 :->: V 3 :&&: T
type P2 = P1 :->: P1

type C1 = O -- empty context 
type C2 = P2 ::: P1 ::: O

data (:=>:) (ctx :: Context) (p :: Formula) where
    ---------------------------------------------
    Assume  :: 
                ------------------
                (p ::: ctx) :=>: p

    ---------------------------------------------
    Weaken  ::         ctx  :=>: q    
                ------------------
            ->  (p ::: ctx) :=>: q

    ---------------------------------------------
    TrueI   :: 
                -----------
                ctx :=>: T

    ----------------------------------------------
    AndI    ::  ctx :=>: p 
            ->  ctx :=>: q 
                -------------------
            ->  ctx :=>: (p :&&: q)

    ----------------------------------------------
    AndE1   ::  ctx :=>: (p :&&: q) 
                -------------------
            ->  ctx :=>: p

    ----------------------------------------------
    AndE2   ::  ctx :=>: (p :&&: q) 
                -------------------
            ->  ctx :=>: q
    
    ----------------------------------------------
    ImpI    ::  (p ::: ctx) :=>: q  
                ------------------
            ->  ctx :=>: (p :->: q)

    ----------------------------------------------
    ImpE    ::  ctx :=>: (p :->: q) 
            ->  ctx :=>: p 
                -------------------
            ->  ctx :=>: q

lemma1 :: forall p ctx . ctx :=>: p :->: p :&&: p
lemma1 = ImpI (AndI Assume Assume) 

lemma2 :: forall p q ctx . ctx :=>: p :&&: q :->: q :&&: p 
lemma2 = ImpI (AndI (AndE2 Assume) (AndE1 Assume)) 

lemma3 :: forall p q r ctx . ctx :=>: (p :&&: q) :&&: r :->: p :&&: (q :&&: r) 
lemma3 = ImpI (AndI (AndE1  (AndE1 Assume)) 
                    (AndI   (AndE2 (AndE1 Assume)) 
                            (AndE2 Assume))) 

deduction :: forall p q ctx . ctx :=>: p :->: q -> p ::: ctx :=>: q
deduction pr = ImpE (Weaken pr) Assume

and1 :: forall p q r ctx . ctx :=>: p :->: q :->: r -> ctx :=>: p :&&: q :->: r
and1 pr = ImpI (ImpE (ImpE (Weaken pr) (AndE1 Assume)) (AndE2 Assume))

and2 :: forall p q r ctx . ctx :=>: p :&&: q :->: r -> ctx :=>: p :->: q :->: r
and2 pr = ImpI (ImpI (ImpE  (Weaken (Weaken pr)) 
                            (AndI (Weaken Assume) Assume)))

and3 :: forall p q r ctx . ctx :=>: p :&&: q :->: r -> ctx :=>: q :&&: p :->: r
and3 pr = ImpI (ImpE (Weaken pr) (AndI (AndE2 Assume) (AndE1 Assume)))


