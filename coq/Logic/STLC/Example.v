Require Import Logic.Class.Eq.

Require Import Logic.STLC.Eval.
Require Import Logic.STLC.Value.
Require Import Logic.STLC.Subst.
Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.Replace.

Definition id (b v:Type)(x:v) : Exp b v := 
    Lam x (Var x). 

Arguments id {b} {v}.

Definition const (b v:Type) (x y:v) : Exp b v :=
    Lam x (Lam y (Var x)).

Arguments const {b} {v}.

Lemma idAnn : forall (b v:Type) (e:Eq v) (x y:v) (a:T b),
    Eval (App (Ann (id x) (Fun a a)) (Var y)) (Var y).
Proof.
    intros b v e x y a. apply (EAppL (Ann (id x) (Fun a a)) (Var x) _ _ x).
    - apply VVar.
    - apply VVar.
    - constructor. apply VLam, VVar. apply ELam.
        + apply VVar.
        + constructor.
    - rewrite substVar. rewrite replace_x. constructor.
Qed.


