Require Import Logic.Class.Eq.

Require Import Logic.STLC.Subst.
Require Import Logic.STLC.Value.
Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.Replace.

(* Big step semantics of STLC                                                   *)
(* EVar: a variable evaluates to itself                                         *)
(* EAnn: if a term evaluates to a value, the annotated term evaluates to same   *)
(* ELam: if a term evaluates to a value, abstracting preserves evaluation       *) 
(* EAppN: evaluation for application, neutral case                              *)
(* EAppL: evaluation for application, lambda case                               *)
Inductive Eval (b v:Type)(e:Eq v) : Exp b v -> Exp b v -> Prop :=
| EVar : forall (x:v), Eval b v e (Var x) (Var x)
| EAnn : forall (t t':Exp b v) (Ty:T b),
    Value t' -> Eval b v e t t' -> Eval b v e (Ann t Ty) t' 
| ELam : forall (t t':Exp b v) (x:v),
    Value t' -> Eval b v  e t t' -> Eval b v e (Lam x t) (Lam x t') 
| EAppN : forall (t1 t1' t2 t2':Exp b v),
    Neutral t1'         -> 
    Value t2'           -> 
    Eval b v e t1 t1'   -> 
    Eval b v e t2 t2'   ->  
    Eval b v e (App t1 t2) (App t1' t2')
| EAppL : forall (t1 t1' t2 t2':Exp b v) (x:v),
    Value t1'                               ->
    Value t2'                               ->
    Eval b v e t1 (Lam x t1')               ->
    Eval b v e (subst (t2 // x) t1') t2'    ->
    Eval b v e (App t1 t2) t2'
.

Arguments Eval  {b} {v} {e}.
Arguments EVar  {b} {v} {e}.
Arguments EAnn  {b} {v} {e}.
Arguments ELam  {b} {v} {e}.
Arguments EAppN {b} {v} {e}.
Arguments EAppL {b} {v} {e}.


Notation "t >> t'" := (Eval t t')
    (at level 90, no associativity) : STLC_Eval_scope.

Open Scope STLC_Eval_scope.


