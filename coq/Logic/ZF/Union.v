Declare Scope ZF_Union_scope.
Open    Scope ZF_Union_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Define.
Require Import Logic.ZF.Extensionality.
Require Import Logic.ZF.Pairing.

(* Given a set a, there exists a set b whose elements are the elements of all   *)
(* the elements of a. More formally:                                            *)
Axiom Union : forall a, exists b,
  forall x, x :< b <-> exists y, x :< y /\ y :< a.

(* It is useful to define the predicate underlying the union axiom.             *)
Definition UnionPred (a:U) : U -> Prop := fun b =>
  forall x, x :< b <-> exists y, x :< y /\ y :< a.

(* The union predicate of the set a is satisfied by at least one set.           *)
Proposition UnionExists : forall (a:U), Exists (UnionPred a).
Proof.
  intros a. apply Union.
Qed.

(* The union predicate of the set a is satisfied by no more than one set.       *)
Proposition UnionUnique : forall (a:U), Unique (UnionPred a).
Proof.
  intros a. unfold Unique. apply SameCharacEqual.
Qed.

(* We consider the set defined by the union predicate of the set a.             *)
Definition UnionSet (a:U) : U
  := Define (UnionPred a) (UnionExists a) (UnionUnique a).

Notation "a :\/: b" := (UnionSet :{a,b}: )
  (at level 3, left associativity) : ZF_Union_scope.

(* The union set of a satisfies the union predicate of a.                       *)
Proposition UnionSatisfy : forall (a:U), UnionPred a (UnionSet a).
Proof.
  intros a. unfold UnionSet. apply DefineSatisfy.
Qed.

(* Characterisation of the elements of the union set of a.                      *)
Proposition UnionCharac : forall (a:U),
  forall x, x :< (UnionSet a) <-> exists y, x :< y /\ y :< a.
Proof.
  apply UnionSatisfy.
Qed.




