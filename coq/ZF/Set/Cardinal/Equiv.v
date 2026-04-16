Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Id.

Require Import ZF.Notation.Equiv.
Export ZF.Notation.Equiv.


Definition equiv (a b:U) : Prop := exists f, Bij f a b.

(* Notation "a :~: b" := (equiv a b)                                            *)
Global Instance Equiv : Equiv U := { equiv := equiv }.

Proposition Refl : forall (a:U), a :~: a.
Proof.
  intros a. exists (id a). apply Id.IsBij.
Qed.

Proposition Sym : forall (a b:U), a :~: b -> b :~: a.
Proof.
  intros a b [f H1]. exists f^:-1:. apply Bij.Converse. assumption.
Qed.

Proposition Tran : forall (a b c:U), a :~: b -> b :~: c -> a :~: c.
Proof.
  intros a b c [f H1] [g H2]. exists (g :.: f).
  apply Bij.Compose with b; assumption.
Qed.


