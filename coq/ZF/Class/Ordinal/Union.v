Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.

(* The union of a class of ordinals is an ordinal class.                        *)
Proposition IsOrdinal : forall (A:Class),
  A :<=: On -> Ordinal :U(A).
Proof.
  intros A H1. assert (:U(A) :<=: On) as H2. { intros a H2.
    destruct H2 as [b [H2 H3]]. apply Core.IsOrdinal with (toClass b).
    2: assumption. apply H1. assumption. }
  apply TransitiveInclIsOrdinal with On; try assumption.
  1: apply OnIsOrdinal. intros a H3. destruct H3 as [b [H3 H4]].
  assert (Ordinal (toClass b)) as H5. { apply H1. assumption. }
  assert (Transitive (toClass b)) as H6. { apply H5. }
  assert (a :<=: b) as H7. { apply H6. assumption. }
  intros x H8. exists b. split. 2: assumption. apply H7. assumption.
Qed.

(* The union of a class of ordinals is an 'upper-bound' of that class.          *)
Proposition IsUpperBound : forall (A:Class) (a:U),
  A :<=: On -> A a -> toClass a :<=: :U(A).
Proof.
  intros A a H1 H2. assert (Ordinal :U(A)) as H3. {
    apply IsOrdinal. assumption. }
    intros x H4. exists a. split; assumption.
Qed.

(* The union of a class of ordinals is its smallest 'upper-bound'.              *)
Proposition IsSmallest : forall (A:Class) (a:U),
  A :<=: On                   ->
  (forall b, A b -> b :<=: a) ->
  :U(A) :<=: toClass a.
Proof.
  intros A a H1 H3 b H4. assert (On b) as H5. {
    apply Core.IsOrdinal with :U(A). 2: assumption.
    apply IsOrdinal. assumption. }
    destruct H4 as [c [H4 H6]]. assert (On c) as H7. {
      apply H1. assumption. }
    apply (H3 c); assumption.
Qed.
