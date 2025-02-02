Require Import ZF.Axiom.Classic.
Require Import ZF.Class.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionalAt.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that y is the value of F at a.                 *)
Definition IsValueAt (F:Class) (a y:U) : Prop := F :(a,y): /\ FunctionalAt F a.

(* When F is functional at a, y being a value of F at a reduces to F (a,y).     *)
Proposition IsValueAtWhenFunctionalAt : forall (F:Class) (a y:U),
  FunctionalAt F a -> IsValueAt F a y <-> F :(a,y):.
Proof.
  intros F a y H1. split; intros H2.
  - destruct H2 as [H2 _]. assumption.
  - split; assumption.
Qed.

(* Whem F is functional, y being a value of F at a reduces to F (a,y).          *)
Proposition IsValueAtWhenFunctional : forall (F:Class) (a y:U),
  Functional F -> IsValueAt F a y <-> F :(a,y):.
Proof.
  intros F a y H1. apply IsValueAtWhenFunctionalAt.
  apply FunctionalIsFunctionalAt. assumption.
Qed.

(* Predicate expressing the fact that the class F has a value at a.             *)
Definition HasValueAt (F:Class) (a:U) : Prop := exists y, IsValueAt F a y.

(* The class HasValueAt F is an intersection.                                   *)
Proposition HasValueAtAsInter : forall (F:Class),
  HasValueAt F :~: FunctionalAt F :/\: domain F.
Proof.
  intros F a. split; intros H1.
  - destruct H1 as [y [H1 H2]]. apply InterCharac. split. 1: assumption.
    apply DomainCharac. exists y. assumption.
  - apply (proj1 (InterCharac _ _ _)) in H1. destruct H1 as [H1 H2].
    apply (proj1 (DomainCharac _ _)) in H2. destruct H2 as [y H2].
    exists y. apply IsValueAtWhenFunctionalAt; assumption.
Qed.

Proposition HasValueAtWhenFunctionalAt : forall (F:Class) (a:U),
  FunctionalAt F a -> HasValueAt F a <-> domain F a.
Proof.
  intros F a H1. split; intros H2.
  - apply HasValueAtAsInter in H2. apply (proj1 (InterCharac _ _ _)) in H2.
    destruct H2 as [_ H2]. assumption.
  - apply HasValueAtAsInter, InterCharac. split; assumption.
Qed.

(* When F is functional, the classes HasValueAt F and domain F coincide.        *)
Proposition HasValueAtWhenFunctional : forall (F:Class),
  Functional F -> HasValueAt F :~: domain F.
Proof.
  intros F H1 a.
  apply HasValueAtWhenFunctionalAt, FunctionalIsFunctionalAt. assumption.
Qed.

(* Evaluate the class F at a.                                                   *)
Definition eval (F:Class) (a:U) : Class := fun x =>
  exists y, x :< y /\ IsValueAt F a y.

(* If F has a value at a, then y corresponds to a iff eval F a = y.             *)
Proposition EvalWhenHasValueAt : forall (F:Class) (a y:U),
  HasValueAt F a -> F :(a,y): <-> eval F a :~: toClass y.
Proof.
  intros F a y H1. split; intros H2.
  - intros x. split; intros H3.
    + unfold eval in H3. destruct H3 as [y' [H3 H4]]. unfold IsValueAt in H4.
      destruct H4 as [H4 H5].
      assert (y = y') as H6. { apply H5; assumption. } subst. assumption.
    + unfold HasValueAt in H1. destruct H1 as [y' [H1 H4]].
      unfold eval. exists y. split. 1: assumption. unfold IsValueAt.
      split; assumption.
  - destruct H1 as [y' [H1 H3]]. assert (y = y') as H4. 2: { subst. assumption. }
    apply SameClassEqual. apply ClassEquivTran with (eval F a).
    + apply ClassEquivSym. assumption.
    + clear H2 y. intros x. split; intros H4.
      * unfold eval in H4. destruct H4 as [y [H4 H5]]. unfold IsValueAt in H5.
        destruct H5 as [H5 H6]. assert (y' = y) as H7. { apply H6; assumption. }
        subst. assumption.
      * exists y'. split. 1: assumption. unfold IsValueAt. split; assumption.
Qed.

(* If F is functional at a and a lies in domain then F (a,y) iff eval F a = y.  *)
Proposition EvalWhenFunctionalAt : forall (F:Class) (a y:U),
  FunctionalAt F a -> domain F a -> F :(a,y): <-> eval F a :~: toClass y.
Proof.
  intros F a y H1 H2.
  apply EvalWhenHasValueAt, HasValueAtWhenFunctionalAt; assumption.
Qed.

(* If F is functional and a lies in domain of F then F (a,y) iff eval F a = y.  *)
Proposition EvalWhenFunctional : forall (F:Class) (a y:U),
  Functional F -> domain F a -> F :(a,y): <-> eval F a :~: toClass y.
Proof.
  intros F a y H1 H2.
  apply EvalWhenHasValueAt, HasValueAtWhenFunctional; assumption.
Qed.

(* If F has no value at a then eval F a is the empty class.                     *)
Proposition EvalWhenNotHasValueAt : forall (F:Class) (a:U),
  ~ HasValueAt F a -> eval F a :~: :0:.
Proof.
  intros F a H1 x. split; intros H2.
  - apply H1. unfold eval in H2. destruct H2 as [y [H2 H3]].
    destruct H3 as [H3 H4]. exists y. split; assumption.
  - apply EmptyCharac in H2. contradiction.
Qed.

(* If F is not functional at a then eval F a is the empty class.                *)
Proposition EvalWhenNotFunctionalAt : forall (F:Class) (a:U),
  ~ FunctionalAt F a -> eval F a :~: :0:.
Proof.
  intros F a H1. apply EvalWhenNotHasValueAt. intros H2. apply H1.
  apply HasValueAtAsInter. assumption.
Qed.

(* If a is not in domain of F then eval F a is the empty class.                 *)
Proposition EvalWhenNotInDomain : forall (F:Class) (a:U),
  ~ domain F a -> eval F a :~: :0:.
Proof.
  intros F a H1. apply EvalWhenNotHasValueAt. intros H2. apply H1.
  apply HasValueAtAsInter. assumption.
Qed.

(* The value of F at a is a always a small class.                               *)
Proposition EvalIsSmall : forall (F:Class) (a:U), Small (eval F a).
Proof.
  (* Let F be an arbitrary class. *)
  intros F.

  (* Let a be an arbitrary set. *)
  intros a.

  (* Either F has a value at a or it has not. *)
  assert (HasValueAt F a \/ ~ HasValueAt F a) as H1. { apply LawExcludedMiddle. }

  (* We consider these two cases separately. *)
  destruct H1 as [H1|H1].

  (* So we assume that F as a value at a. *)
  - assert (HasValueAt F a) as A. { apply H1. } clear A.

  (* Let y be a value of F at a. *)
    assert (H2 := H1). destruct H2 as [y H2].
    assert (IsValueAt F a y) as A. { apply H2. } clear A.

  (* In particular we have F (a,y) *)
    destruct H2 as [H2 _].
    assert (F :(a,y):) as A. { apply H2. } clear A.

  (* And it follows that eval F a = y. *)
    assert (eval F a :~: toClass y) as H3.
       { apply EvalWhenHasValueAt; assumption. }

  (* Using this equivalence ... *)
    apply SmallEquivCompat with (toClass y). 1: { apply ClassEquivSym, H3. }

  (* We simply need to show that the set y is small *)
    assert (Small (toClass y)) as A. 2: apply A.

  (* Which is clear. *)
    apply SetIsSmall.

  (* We now assume that F as no value at a. *)
  - assert (~ HasValueAt F a) as A. { apply H1. } clear A.

  (* Then eval F a is the empty class. *)
    assert (eval F a :~: :0:) as H2. { apply EvalWhenNotHasValueAt, H1. }

  (* Using this equivalence ... *)
    apply SmallEquivCompat with :0:. 1: { apply ClassEquivSym, H2. }

  (* We simply need to show that the empty class is small. *)
    assert (Small :0:) as A. 2: apply A.

  (* Which we know is true. *)
    apply EmptyIsSmall.
Qed.
