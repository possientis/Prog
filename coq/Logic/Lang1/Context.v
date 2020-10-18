Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Nat.Eq.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.

Require Import Logic.Lang1.Syntax.

(* Custom notations for predicates of 3 arguments appear to fail in Coq.        *)
(* Creating intermediary types Binding and Interpretation to bypass the issue.  *)
Inductive Binding : Type :=
| mkBind : forall (n:nat) (x:set), Binding
.

Notation "n ~> x" := (mkBind n x)
    (at level 1, no associativity) : Context_scope.

Inductive Context : Type :=
| O        : Context
| CtxSnoc  : Context -> Binding -> Context
.

Notation "G ';' x" := (CtxSnoc G x)
    (at level 50, left associativity) : Context_scope.

Open Scope Context_scope.

Inductive Find : Context -> Binding -> Prop :=
| FindZ : forall (G:Context) (n:nat) (x:set), Find (G ; n~>x) n~>x
| FindS : forall (G:Context) (n m:nat) (x y:set),
    n <> m      -> 
    Find G n~>x -> 
    Find (G ; m~>y) n~>x
.

Notation "G ':>' x" := (Find G x)
    (at level 60, no associativity) : Context_scope.

Open Scope Context_scope.

(* Just restating constructor FindZ with custom notations.                      *)
Lemma findZ : forall (G:Context) (n:nat) (x:set), G ; n~>x :> n~>x. 
Proof.
    intros G n x. constructor.
Qed.

(* Just restating constructor FindS with custom notations.                      *)
Lemma findS : forall (G:Context) (n m:nat) (x y:set),
    n <> m -> G :> n~>x -> G ; m~>y :> n~>x.
Proof.
    intros G n m x y H1 H2. constructor; assumption.
Qed.

Definition ctxIncl (G H:Context) : Prop :=
    forall (n:nat) (x:set), G :> n~>x -> H :> n~>x.

Notation "G <= H"  := (ctxIncl G H)
    (at level 70, no associativity) : Context_scope.

Open Scope Context_scope.

(* The corresponding proof in agda appears to be a lot simpler.                 *)
Lemma ctxInclExtend : forall (G H:Context) (n:nat) (x:set),
    G <= H -> G ; n~>x <= H ; n~>x.
Proof.
    intros G H n x. unfold ctxIncl. intros H2 m y H3.
    remember (G ; n~>x) as G' eqn:G1. remember (H ; n~>x) as H' eqn:H1. 
    remember (m~>y) as b eqn:H4.
    revert m y H H' G n x H4 H2 G1 H1.
    destruct H3 as [G' n' x'|G' n' m' x' y' Hnm H1]; 
    intros n x H H' G m y H2 H3 H4 H5; inversion H2; subst; clear H2;
    inversion H4; subst; clear H4.
    - apply findZ.
    - apply findS; try assumption. apply H3. assumption.
Qed.

Lemma ctxInclRefl : forall (G:Context), G <= G.
Proof.
    unfold ctxIncl. intros G n x. auto.
Qed.

Lemma ctxInclTrans : forall (G H K:Context), G <= H -> H <= K -> G <= K.
Proof.
    unfold ctxIncl. intros G H K H1 H2 n x H3. apply H2, H1. assumption.
Qed.


Definition ctxEqual (G G':Context) : Prop := G <= G' /\ G' <= G.

Lemma ctxEqualRefl : forall (G:Context), ctxEqual G G.
Proof.
    intros G. split; apply ctxInclRefl.
Qed.

Lemma ctxEqualSym : forall (G G':Context), ctxEqual G G' -> ctxEqual G' G.
Proof.
    intros G G' [H1 H2]. split; assumption.
Qed.

Lemma ctxEqualTrans : forall (G1 G2 G3:Context), 
    ctxEqual G1 G2 -> ctxEqual G2 G3 -> ctxEqual G1 G3.
Proof.
    intros G1 G2 G3 [H1 H2] [H3 H4]. split; 
    apply ctxInclTrans with G2; assumption.
Qed.

Definition ctxEqualOn (p:Formula) (G G':Context) : Prop :=
    forall (n:nat) (x:set), In n (Fr p) -> G :> n~>x <-> G' :> n~>x.

Lemma ctxEqualOnRefl : forall (p:Formula) (G:Context), ctxEqualOn p G G.
Proof.
    intros p G n x H1. split; auto.
Qed.

Lemma ctxEqualOnSym : forall (p:Formula) (G G':Context),
    ctxEqualOn p G G' -> ctxEqualOn p G' G.
Proof.
    intros p G G' H1 n x H2. destruct (H1 n x H2) as [H3 H4]. split; assumption.
Qed.

Lemma ctxEqualOnTrans : forall (p:Formula) (G1 G2 G3: Context),
    ctxEqualOn p G1 G2 -> ctxEqualOn p G2 G3 -> ctxEqualOn p G1 G3.
Proof.
    intros p G1 G2 G3 H1 H2 n x H3. 
    destruct (H1 n x H3) as [H4 H5].
    destruct (H2 n x H3) as [H6 H7]. split; intros H8.
    - apply H6, H4. assumption.
    - apply H5, H7. assumption.
Qed.

Lemma ctxEqualctxEqualOn : forall (p:Formula) (G G':Context),
    ctxEqual G G' -> ctxEqualOn p G G'.
Proof.
    intros p G G' [H1 H2] n x H3. split.
    - apply H1.
    - apply H2.
Qed.

(* Not very useful. Just following the parallel with Environment.               *)
Definition bind (G:Context) (n:nat) (x:set) : Context := G ; n~>x. 

