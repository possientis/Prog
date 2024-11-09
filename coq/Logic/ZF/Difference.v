Declare Scope ZF_Difference_scope.
Open    Scope ZF_Difference_scope.

Require Import Logic.ZF.Classic.
Require Import Logic.ZF.Core.
Require Import Logic.ZF.Empty.
Require Import Logic.ZF.Extensionality.
Require Import Logic.ZF.Include.
Require Import Logic.ZF.Intersect.
Require Import Logic.ZF.Specification.
Require Import Logic.ZF.Union.

(* The set a \ b is made of those elements of a which do not belong to b.       *)
Definition difference (a b:U) : U := :{a | fun x => ~ x :< b }:.

Notation "a :\: b" := (difference a b)
  (at level 3, no associativity) : ZF_Difference_scope.

Proposition DiffCharac : forall (a b:U),
  forall x, x :< a:\:b <-> x :< a /\ ~ x :< b.
Proof.
  intros a b x. unfold difference. apply SpecCharac.
Qed.

Proposition DiffEmptyInclude : forall (a b:U),
  a :\: b = :0: <-> a :<=: b.
Proof.
  intros a b. split; intros H1.
  - intros x Ha. apply DoubleNegation. intros Hb.
    assert (x :< :0:) as H2.
      { rewrite <- H1. apply DiffCharac. split; assumption. }
    apply EmptyCharac in H2. contradiction.
  - apply Extensionality. intros x. split; intros H2.
    + apply DiffCharac in H2. destruct H2 as [H2 H3].
      apply H1 in H2. contradiction.
    + apply EmptyCharac in H2. contradiction.
Qed.

(*
Proposition DiffUnionIntersect : forall (a b c:U),
  a :\: (b:\/:c) = a:\:b :/\: a:\:c.
Proof.

Show.
*)
