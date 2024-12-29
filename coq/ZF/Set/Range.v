Require Import ZF.Class.
Require Import ZF.Class.Range.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

(* The range of a set.                                                          *)
Definition range (a:U) : U := fromClass
  (Class.Range.range (toClass a))
  (RangeIsSmall (toClass a) (SetIsSmall a)).

Proposition RangeCharac : forall (a:U),
  forall y, y :< (range a) <-> exists x, :(x,y): :< a.
Proof.
  intros a y. unfold range. split; intros H1.
  - apply FromClassCharac, (proj1 (Class.Range.RangeCharac _ _)) in H1.
    apply H1.
  - apply FromClassCharac, Class.Range.RangeCharac, H1.
Qed.
