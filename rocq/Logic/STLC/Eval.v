Require Import Logic.Class.Eq.

Require Import Logic.STLC.Subst.
Require Import Logic.STLC.Value.
Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.Replace.

Declare Scope STLC_Eval_scope.

(* Big step semantics of STLC                                                   *)
(* EVar: a variable evaluates to itself                                         *)
(* EAnn: if a term evaluates to a value, the annotated term evaluates to same   *)
(* ELam: if a term evaluates to a value, abstracting preserves evaluation       *) 
(* EAppN: evaluation for application, neutral case                              *)
(* EAppL: evaluation for application, lambda case                               *)
Inductive Eval (b v:Type)(eq:Eq v) : Exp b v -> Exp b v -> Prop :=
| EVar : forall (x:v), Eval b v eq (Var x) (Var x)
| EAnn : forall (e e':Exp b v) (Ty:T b),
    Value e' -> Eval b v eq e e' -> Eval b v eq (Ann e Ty) e' 
| ELam : forall (e e':Exp b v) (x:v),
    Value e' -> Eval b v eq e e' -> Eval b v eq (Lam x e) (Lam x e') 
| EAppN : forall (e1 e1' e2 e2':Exp b v),
    Neutral e1'         -> 
    Value e2'           -> 
    Eval b v eq e1 e1'  -> 
    Eval b v eq e2 e2'  ->  
    Eval b v eq (App e1 e2) (App e1' e2')
| EAppL : forall (e1 e1' e2 e2':Exp b v) (x:v),
    Value e1'                               ->
    Value e2'                               ->
    Eval b v eq e1 (Lam x e1')              ->
    Eval b v eq (subst (e2 // x) e1') e2'   ->
    Eval b v eq (App e1 e2) e2'
.

Arguments Eval  {b} {v} {eq}.
Arguments EVar  {b} {v} {eq}.
Arguments EAnn  {b} {v} {eq}.
Arguments ELam  {b} {v} {eq}.
Arguments EAppN {b} {v} {eq}.
Arguments EAppL {b} {v} {eq}.


Notation "e >>> e'" := (Eval e e')
    (at level 90, no associativity) : STLC_Eval_scope.

Open Scope STLC_Eval_scope.
