Require Import ZF.Binary.Domain.
Require Import ZF.Class.
Require Import ZF.Class.Binary.
Require Import ZF.Class.Include.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* The domain of a class is the domain of its binary class.                     *)
Definition domain (P:Class) : Class := Domain.domain (toBinary P).

(* Quick unfolding.                                                             *)
Proposition DomainCharac : forall (P:Class) (x:U),
  domain P x <-> exists y, P :(x,y):.
Proof.
  intros P x. split; intros H1.
  - apply H1.
  - apply H1.
Qed.

Proposition DomainMonotone : forall (P Q:Class),
  P :<=: Q -> domain P :<=: domain Q.
Proof.
  intros P Q H1 x H2. apply (proj1 (DomainCharac P x)) in H2. destruct H2 as [y H2].
  apply DomainCharac. exists y. apply H1, H2.
Qed.


