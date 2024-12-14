Declare Scope ZF_Axiom_Specification_scope.
Open    Scope ZF_Axiom_Specification_scope.

Require Import ZF.Axiom.Specification.
Require Import ZF.Class.Small.
Require Import ZF.Set.

(* It is useful to define the predicate underlying the specification axiom.     *)
Definition SpecPred (P:U -> Prop) (a:U) : U -> Prop := fun x =>
  x :< a /\ P x.

(* The specification predicate of a and P is small                              *)
Proposition SpecSmall : forall (P:U -> Prop) (a:U),
    Small (SpecPred P a).
Proof.
  apply Specification.
Qed.

(* We consider the set defined by the specification predicate of P and a.       *)
Definition specSet (P:U -> Prop) (a:U) : U
  := toSet (SpecPred P a) (SpecSmall P a).

Notation ":{ a | P }:" := (specSet P a)
  (at level 1, no associativity) : ZF_Axiom_Specification_scope.

(* Characterisation of the elements of {a :| P}.                                *)
Proposition SpecCharac : forall (P:U -> Prop) (a:U),
  forall x, x :< :{a | P}: <-> x :< a /\ P x.
Proof.
  unfold specSet. intros P a. apply ClassCharac.
Qed.

(* Every element of the specification set of P and a is an element of a.        *)
Proposition SpecInInA : forall (P:U -> Prop) (a:U),
  forall x, x :< :{a | P}: -> x :< a.
Proof.
  intros P a x H1. apply SpecCharac in H1. destruct H1 as [H1 _]. apply H1.
Qed.

(* Every element of the specification set of P and a satisfies the predicate P. *)
Proposition SpecInP : forall (P:U -> Prop) (a:U),
  forall x, x :< :{a | P}: -> P x.
Proof.
  intros P a x H1. apply SpecCharac in H1. destruct H1 as [_ H1]. apply H1.
Qed.

(* If a set belongs to a set a and satisfies the predicate P, then it belongs   *)
(* to the specification set of P and a.                                         *)
Proposition SpecInAPIn: forall (P:U -> Prop) (a:U),
  forall x, x :< a -> P x -> x :< :{a | P}:.
Proof.
  intros P a x H1 H2. apply SpecCharac. split; assumption.
Qed.
