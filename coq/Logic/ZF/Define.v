Require Import Logic.ZF.Core.

(* Predicate over set theoretic predicates, expressing the fact that the        *)
(* predicate is satisfied by at least one set                                   *)
Definition Exists (P:U -> Prop) : Prop := exists x, P x.

(* Predicate over set theoretic predicates, expressing the fact that the        *)
(* predicate is satisfied by no more than one set                               *)
Definition Unique (P:U -> Prop) : Prop := forall a b, P a -> P b -> a = b.

(* When a set theoretic predicate is satisfied by a unique set, we can define   *)
(* such a set                                                                   *)
Axiom Define : forall (P:U -> Prop), Exists P -> Unique P -> U.

(* The set defined by a predicate which is uniquely satisfied, does satisfy the *)
(* predicate in question                                                        *)
Axiom DefineSatisfy: forall (P:U -> Prop) (p:Exists P) (q:Unique P),
    P(Define P p q).

(* The set defined by a predicate which is uniquely satisfied is unique         *)
Proposition DefineUnique : forall (P:U -> Prop) (p:Exists P) (q:Unique P),
  forall x, P x -> x = Define P p q.
Proof.
  intros P p q x Hx. apply q.
  - apply Hx.
  - apply DefineSatisfy.
Qed.

(* The set defined by a predicate which is uniquely satisfied is the same       *)
(* regardless of the proofs used to define it.                                  *)
Proposition DefineProof : forall (P:U -> Prop) (p p':Exists P) (q q':Unique P),
  Define P p q = Define P p' q'.
Proof.
  intros P p p' q q'. apply DefineUnique, DefineSatisfy.
Qed.
