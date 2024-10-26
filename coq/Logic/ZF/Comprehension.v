Require Import Logic.ZF.Core.
Require Import Logic.ZF.Define.
Require Import Logic.ZF.Extensionality.

(* Given a set theoretic predicate P and a set a, there exists a set b whose    *)
(* elements are the elements of the set a which satisfy P.                      *)
Axiom Comprehension : forall (P:U -> Prop),
  forall a, exists b, forall x, x :< b <-> x :< a /\ P x.

(* It is useful to define the predicate underlying the comprehension axiom      *)
Definition CompPred (P:U -> Prop) (a:U) : U -> Prop := fun b =>
  forall x, x :< b <-> x :< a /\ P x.

(* The comprehension predicate of P and a is satisfied by at least one set .    *)
Proposition CompExists: forall (P:U -> Prop) (a:U),
    Exists (CompPred P a).
Proof.
  intros P a. apply Comprehension.
Qed.

(* The comprehension predicate of P and a is satisfied by no more than one set. *)
Proposition CompUnique: forall (P:U -> Prop) (a:U),
    Unique (CompPred P a).
Proof.
  intros P a. unfold Unique. apply SameCharacEqual.
Qed.

(* We consider the set defined by the comprehension predicate of P and a.       *)
Definition CompSet (P:U -> Prop) (a:U) : U
  := Define (CompPred P a) (CompExists P a) (CompUnique P a).

(* The comprehension set of P and a satisfies its comprehension predicate.      *)
Proposition CompSatisfy : forall (P:U -> Prop) (a:U),
  CompPred P a (CompSet P a).
Proof.
  intros P a. unfold CompSet. apply DefineSatisfy.
Qed.

(* Characterisation of the elements of the comprehension set of P and a.        *)
Proposition CompCharac : forall (P:U -> Prop) (a:U),
  forall x, x :< (CompSet P a) <-> x :< a /\ P x.
Proof.
  apply CompSatisfy.
Qed.

(* Every element of the comprehension set of P and a is an element of a.        *)
Proposition CompA : forall (P:U -> Prop) (a:U),
  forall x, x :< (CompSet P a) -> x :< a.
Proof.
  intros P a x Hx.
  assert (CompPred P a (CompSet P a)) as H.
    { apply CompSatisfy. }
  unfold CompPred in H.
  apply H in Hx. destruct Hx as [H1 H2].
  apply H1.
Qed.

(* Every element of the comprehension set of P and a satisfies the predicate P. *)
Proposition CompP : forall (P:U -> Prop) (a:U),
  forall x, x :< (CompSet P a) -> P x.
Proof.
  intros P a x Hx.
  assert (CompPred P a (CompSet P a)) as H.
    { apply CompSatisfy. }
  unfold CompPred in H.
  apply H in Hx. destruct Hx as [H1 H2].
  apply H2.
Qed.

(* If a set belongs to a set a and satisfies the predicate P, then it belongs   *)
(* to the comprehension set of P and a.                                         *)
Proposition CompIn: forall (P:U -> Prop) (a:U),
  forall x, x :< a -> P x -> x :< (CompSet P a).
Proof.
  intros P a x H1 H2.
  assert (CompPred P a (CompSet P a)) as H.
    { apply CompSatisfy. }
  unfold CompPred in H. apply H.
  split.
    - apply H1.
    - apply H2.
Qed.
