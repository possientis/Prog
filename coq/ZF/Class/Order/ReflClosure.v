Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.AntiSymmetric.
Require Import ZF.Class.Order.Irreflexive.
Require Import ZF.Class.Order.Reflexive.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.ReflClosure.
Export ZF.Notation.ReflClosure.

(* The reflexive closure of a class.                                            *)
Definition reflClosure (R:Class) : Class := fun x =>
  (exists y, x = :(y,y):) \/ R x.

(* Notation "R ^:=:" := (reflClosure R)                                         *)
Global Instance ClassReflClosure : ReflClosure Class
  := { reflClosure := reflClosure }.

(* The class is a subclass of its reflexive closure,                            *)
Proposition IsIncl : forall (R:Class), R :<=: R^:=:.
Proof.
  intros R x H1. right. assumption.
Qed.

Proposition Charac2 : forall (R:Class) (y z:U),
  R^:=: :(y,z): <-> y = z \/ R :(y,z):.
Proof.
  intros R y z. split; intros H1; destruct H1 as [H1|H1].
  - destruct H1 as [x H1]. apply OrdPair.WhenEqual in H1.
    destruct H1 as [H1 H2]. subst. left. reflexivity.
  - right. assumption.
  - subst. left. exists z. reflexivity.
  - right. assumption.
Qed.

(* The reflexive closure is compatible with class equivalence.                  *)
Proposition EquivCompat : forall (R S:Class),
  R :~: S -> R^:=: :~: S^:=:.
Proof.
  intros R S H1 x. split; intros [H2|H2].
  - destruct H2 as [y H2]. subst. left. exists y. reflexivity.
  - right. apply H1. assumption.
  - destruct H2 as [y H2]. subst. left. exists y. reflexivity.
  - right. apply H1. assumption.
Qed.

(* The reflexive closure of R is the smallest reflexive relation containing R.  *)
Proposition IsSmallestOn : forall (R S A:Class) (x y:U),
  Reflexive S A                                       ->
  (forall x y, A x -> A y -> R :(x,y): -> S :(x,y):)  ->
  A x                                                 ->
  A y                                                 ->
  R^:=: :(x,y):                                       ->
  S :(x,y):.
Proof.
  intros R S A x y H1 H2 H3 H4 H5. apply Charac2 in H5. destruct H5 as [H5|H5].
  - subst. apply H1. assumption.
  - apply H2; assumption.
Qed.

(* The reflexive closure is reflexive on any class A.                           *)
Proposition IsReflexive : forall (R A:Class),
  Reflexive R^:=: A.
Proof.
  intros R A x H1. apply Charac2. left. reflexivity.
Qed.

(* The reflexive closure of a transitive class on A is a transitive class on A. *)
Proposition IsTransitive : forall (R A:Class),
  Transitive R A -> Transitive R^:=: A.
Proof.
  intros R A H1 x y z H2 H3 H4 H5 H6.
  apply Charac2 in H5. apply Charac2 in H6.
  destruct H5 as [H5|H5]; destruct H6 as [H6|H6]; apply Charac2; subst.
  - left. reflexivity.
  - right. assumption.
  - right. assumption.
  - right. apply H1 with y; assumption.
Qed.

(* The closure is antisymmetric when the class is irreflexive and transitive.   *)
Proposition IsAntiSymmetric : forall (R A:Class),
  Irreflexive R A -> Transitive R A  -> AntiSymmetric R^:=: A.
Proof.
  intros R A H1 H2 x y H3 H4 H5 H6.
  apply Charac2 in H5. apply Charac2 in H6.
  destruct H5 as [H5|H5]; destruct H6 as [H6|H6]; subst; try reflexivity.
  exfalso. apply H1 with x. 1: assumption. apply H2 with y; assumption.
Qed.

Proposition LeqOrLeq : forall (R A:Class) (x y:U),
  Total R A ->
  A x       ->
  A y       ->
  R^:=: :(x,y): \/ R^:=: :(y,x):.
Proof.
  intros R A x y H1 H2 H3. specialize (H1 x y H2 H3).
  destruct H1 as [H1|[H1|H1]].
  - subst. left. apply Charac2. left. reflexivity.
  - left. apply Charac2. right. assumption.
  - right. apply Charac2. right. assumption.
Qed.

Proposition LessOrLeq : forall (R A:Class) (x y:U),
  Total R A ->
  A x       ->
  A y       ->
  R :(x,y): \/ R^:=: :(y,x):.
Proof.
  intros R A x y H1 H2 H3. specialize (H1 x y H2 H3).
  destruct H1 as [H1|[H1|H1]].
  - subst. right. apply Charac2. left. reflexivity.
  - left. assumption.
  - right. apply Charac2. right. assumption.
Qed.

Proposition LeqLessTran : forall (R A:Class) (x y z:U),
  Transitive R A  ->
  A x             ->
  A y             ->
  A z             ->
  R^:=: :(x,y):   ->
  R :(y,z):       ->
  R :(x,z):.
Proof.
  intros R A x y z H1 H2 H3 H4 H5 H6.
  apply Charac2 in H5. destruct H5 as [H5|H5].
  - subst. assumption.
  - apply H1 with y; assumption.
Qed.

Proposition LessLeqTran : forall (R A:Class) (x y z:U),
  Transitive R A  ->
  A x             ->
  A y             ->
  A z             ->
  R :(x,y):       ->
  R^:=: :(y,z):   ->
  R :(x,z):.
Proof.
  intros R A x y z H1 H2 H3 H4 H5 H6.
  apply Charac2 in H6. destruct H6 as [H6|H6].
  - subst. assumption.
  - apply H1 with y; assumption.
Qed.

