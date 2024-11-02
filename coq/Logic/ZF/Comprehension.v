Declare Scope ZF_Comprehension_scope.
Open    Scope ZF_Comprehension_scope.

Require Import Logic.ZF.Class.
Require Import Logic.ZF.Core.
Require Import Logic.ZF.Extensionality.

(* Given a set theoretic predicate P and a set a, there exists a set b whose    *)
(* elements are the elements of the set a which satisfy P.                      *)
Axiom Comprehension : forall (P:U -> Prop),
  forall a, exists b, forall x, x :< b <-> x :< a /\ P x.

(* It is useful to define the predicate underlying the comprehension axiom.     *)
Definition CompPred (P:U -> Prop) (a:U) : U -> Prop := fun x =>
  x :< a /\ P x.

(* The comprehension predicate of a and P is small                              *)
Proposition CompSmall: forall (P:U -> Prop) (a:U),
    Small (CompPred P a).
Proof.
  apply Comprehension.
Qed.

(* We consider the set defined by the comprehension predicate of P and a.       *)
Definition compSet (P:U -> Prop) (a:U) : U
  := toSet (CompPred P a) (CompSmall P a).

Notation ":{ a | P }:" := (compSet P a)
  (at level 1, no associativity) : ZF_Comprehension_scope.

(* Characterisation of the elements of {a :| P}.                                *)
Proposition CompCharac : forall (P:U -> Prop) (a:U),
  forall x, x :< :{a | P}: <-> x :< a /\ P x.
Proof.
  unfold compSet. intros P a. apply ClassCharac.
Qed.

(* Every element of the comprehension set of P and a is an element of a.        *)
Proposition CompInInA : forall (P:U -> Prop) (a:U),
  forall x, x :< :{a | P}: -> x :< a.
Proof.
  intros P a x H1. apply CompCharac in H1. destruct H1 as [H1 _]. apply H1.
Qed.

(* Every element of the comprehension set of P and a satisfies the predicate P. *)
Proposition CompInP : forall (P:U -> Prop) (a:U),
  forall x, x :< :{a | P}: -> P x.
Proof.
  intros P a x H1. apply CompCharac in H1. destruct H1 as [_ H1]. apply H1.
Qed.

(* If a set belongs to a set a and satisfies the predicate P, then it belongs   *)
(* to the comprehension set of P and a.                                         *)
Proposition CompInAPIn: forall (P:U -> Prop) (a:U),
  forall x, x :< a -> P x -> x :< :{a | P}:.
Proof.
  intros P a x H1 H2. apply CompCharac. split; assumption.
Qed.
