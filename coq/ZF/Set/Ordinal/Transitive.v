Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.

Module COT := ZF.Class.Ordinal.Transitive.

Definition Transitive (a:U) : Prop := forall (x y:U),
  x :< y -> y :< a -> x :< a.

Proposition ToClass : forall (a:U),
  Transitive a <-> COT.Transitive (toClass a).
Proof.
  intros a. split; intros H1.
  - intros y H2 x H3. apply H1 with y; assumption.
  - intros x y H2 H3. apply H1 with y; assumption.
Qed.

Proposition WhenOrdinal : forall (a:U), Ordinal a -> Transitive a.
Proof.
  intros a H1 x y H2 H3.
  assert (Ordinal y) as H4. { apply Core.IsOrdinal with a; assumption. }
  assert (Ordinal x) as H5. { apply Core.IsOrdinal with y; assumption. }
  apply Core.ElemElemTran with y; assumption.
Qed.
