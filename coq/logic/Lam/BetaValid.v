Require Import Eq.
Require Import In.
Require Import Difference.
Require Import Lam.T.
Require Import Lam.Free.

Inductive BetaValid_ (v:Type) (e:Eq v) (f:v -> T v) : list v -> T v -> Prop :=
| VVar : forall (xs:list v) (x:v), BetaValid_ v _ f xs (Var x)
| VApp : forall (xs:list v) (t1 t2:T v), 
    BetaValid_ v _ f xs t1 -> 
    BetaValid_ v _ f xs t2 -> 
    BetaValid_ v _ f xs (App t1 t2)
| VLam : forall (xs:list v) (x:v) (t1:T v),
    BetaValid_ v _ f (cons x xs) t1 ->
    (forall (u:v), u :: Fr (Lam x t1) \\ xs -> ~ x :: Fr (f u)) ->
    BetaValid_ v _ f xs (Lam x t1)  
.
