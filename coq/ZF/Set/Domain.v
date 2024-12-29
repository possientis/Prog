Require Import ZF.Class.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

(* The domain of a set.                                                         *)
Definition domain (a:U) : U := fromClass
  (Class.Domain.domain (toClass a))
  (DomainIsSmall (toClass a) (SetIsSmall a)).

Proposition DomainCharac : forall (a:U),
  forall x, x :< (domain a) <-> exists y, :(x,y): :< a.
Proof.
  intros a x. unfold domain. split; intros H1.
  - apply FromClassCharac, (proj1 (Class.Domain.DomainCharac _ _)) in H1.
    apply H1.
  - apply FromClassCharac, Class.Domain.DomainCharac, H1.
Qed.
