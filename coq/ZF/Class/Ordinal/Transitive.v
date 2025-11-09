Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Less.
Require Import ZF.Class.One.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.

(* Predicate defining a transitive class. Informally: y :< x :< A -> y:< A.     *)
Definition Transitive (A:Class) : Prop := forall x, A x -> toClass x :<=: A.

(* An element of a transitive class defines a strict subclass of that class.    *)
Proposition IsLess : forall (A:Class) (a:U),
  Transitive A -> A a -> toClass a :<: A.
Proof.
  intros A a H1 H2. split.
  - apply H1. assumption.
  - intros H3. apply NoElemLoop1 with a. apply H3. assumption.
Qed.

(* Being a transitive class is compatible with class equivalence.               *)
Proposition EquivCompat : forall (A B:Class),
  A :~: B -> Transitive A -> Transitive B.
Proof.
  intros A B H1 H2 x H3. apply Incl.EquivCompatR with A. 1: assumption.
  apply H2, H1. assumption.
Qed.

Proposition Charac : forall (A:Class),
  Transitive A <-> forall x y, x :< y -> A y -> A x.
Proof.
  intros A. split; intros H1.
  - intros x y H2 H3. unfold Transitive in H1.
    specialize (H1 y H3 x). apply H1. assumption.
  - intros y H2 x H3. apply H1 with y; assumption.
Qed.

Proposition UnionIncl : forall (A:Class),
  Transitive A -> :U(A) :<=: A.
Proof.
  intros A H1 x H2. destruct H2 as [y [H2 H3]]. specialize (H1 y H3 x).
  apply H1. assumption.
Qed.

Proposition ZeroIsTransitive : Transitive :0:.
Proof.
  intros x H1. apply Class.Empty.Charac in H1. contradiction.
Qed.

Proposition OneIsTransitive : Transitive :1:.
Proof.
  intros x H1. rewrite H1. intros y H2. apply Empty.Charac in H2. contradiction.
Qed.

Proposition InterIsIncl: forall (A:Class),
  Transitive A -> A :<>: :0: -> :I(A) :<=: A.
Proof.
  intros A H1 H2 x H3. apply HasElem in H2. destruct H2 as [y H2].
  specialize (H1 y H2). apply H1. apply H3. assumption.
Qed.

