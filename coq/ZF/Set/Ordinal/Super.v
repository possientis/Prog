Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Super.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Transitive.
Require Import ZF.Set.Power.

Module COS := ZF.Class.Ordinal.Super.

(* Predicate defining a supertransitive set.                                    *)
Definition Super (a:U) : Prop := Transitive a /\
  forall x, x :< a -> :P(x) :<=: a.

Proposition ToClass : forall (a:U),
  Super a <-> COS.Super (toClass a).
Proof.
  intros a. split; intros [H1 H2].
  - split.
    + apply Transitive.ToClass. assumption.
    + intros x H3. apply H2. assumption.
  - split.
    + apply Transitive.ToClass. assumption.
    + intros x H3. apply H2. assumption.
Qed.
