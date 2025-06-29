Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

Export ZF.Notation.Dot.

(* Composition of two sets.                                                     *)
Definition compose (g f:U) : U := fromClass (toClass g :.: toClass f)
  (Compose.IsSmall (toClass f) (toClass g) (SetIsSmall f) (SetIsSmall g)).

(* Notation "g :.: f" := (compose g f)                                          *)
Global Instance SetDot : Dot U := { dot := compose }.

(* The class of the composition is the composition of the classes.              *)
Proposition ToClass : forall (f g:U),
  toClass (g :.: f) :~: toClass g :.: toClass f.
Proof.
  intros f g. apply ToFromClass.
Qed.

Proposition Charac : forall (f g u:U),
  u :< (g :.: f) <-> exists x y z, u =:(x,z): /\ :(x,y): :< f /\ :(y,z): :< g.
Proof.
Admitted.
