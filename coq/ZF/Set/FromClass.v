Require Import ZF.Axiom.Define.
Require Import ZF.Class.Core.
Require Import ZF.Class.IsSetOf.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.

(* If a class is small, we can define the set it defines.                       *)
Definition fromClass (A :Class) (p:Small A) : U
  := define (IsSetOf A) (IsSetOf.Exists A p) (IsSetOf.Unique A).

Proposition EquivCompat : forall (A B:Class) (p:Small A) (q:Small B),
  A :~: B -> fromClass A p = fromClass B q.
Proof.
  intros A B p q H1. apply Define.EquivCompat, IsSetOf.EquivCompat. assumption.
Qed.

(* The set defined by a small class belongs to the class of all sets defined.   *)
Proposition IsIn : forall (A:Class) (p:Small A),
  IsSetOf A (fromClass A p).
Proof.
  intros A p. unfold fromClass. apply Define.IsIn.
Qed.

(* Characterisation of the elements of the set defined by a small class.        *)
Proposition Charac : forall (A:Class) (p:Small A),
  forall x, x :< (fromClass A p) <-> A x.
Proof.
  apply IsIn.
Qed.

(* The set defined by a small class does not depend on the proof being used.    *)
Proposition ProofIrrelevant : forall (A:Class) (p q:Small A),
  fromClass A p = fromClass A q.
Proof.
  intros A p q. unfold fromClass. apply Define.ProofIrrelevant.
Qed.

(* The set defined by the class associated with a set is the set itself.        *)
Proposition FromToClass : forall (a:U),
  fromClass (toClass a) (SetIsSmall a) = a.
Proof.
  intro a. apply EqualToClass. intros x. apply Charac.
Qed.

(* The class associated with the set defined by a small class is the class.     *)
Proposition ToFromClass : forall (A:Class) (p:Small A),
  toClass (fromClass A p) :~: A.
Proof.
  intros A p x. apply Charac.
Qed.

(* Belonging to the class of all sets defined, is the same as being defined by  *)
Proposition IsSetOfFrom : forall (A:Class) (a:U) (p:Small A),
  IsSetOf A a <-> a = fromClass A p.
Proof.
  intros A a p. split; intros H1.
  - apply Define.IsUnique. assumption.
  - rewrite H1. apply IsIn.
Qed.
