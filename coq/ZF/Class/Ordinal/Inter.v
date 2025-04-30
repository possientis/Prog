Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.

(* The intersection of a non-empty class of ordinals is a class of ordinals.    *)
Proposition IsIncl : forall (A:Class), A :<=: On -> A :<>: :0: -> :I(A) :<=: On.
Proof.
  intros A H1 H2. apply Class.Empty.HasElem in H2. destruct H2 as [a H2].
  intros x H3. apply Core.IsOrdinal with a.
  - apply H1. assumption.
  - apply H3. assumption.
Qed.

(* The intersection of a class of ordinals is a transitive class.               *)
Proposition IsTransitive : forall (A:Class), A :<=: On -> Transitive :I(A).
Proof.
  intros A H1 y H2 x H3 z H4.
  assert (y :< z) as H5. { apply H2. assumption. }
  assert (Ordinal z) as H6. { apply H1. assumption. }
  assert (Ordinal y) as H7. { apply Core.IsOrdinal with z; assumption. }
  assert (Ordinal x) as H8. { apply Core.IsOrdinal with y; assumption. }
  apply ElemElemTran with y; assumption.
Qed.

(* The Intersection of a non-empty class of ordinals is an ordinal class.       *)
Proposition IsOrdinal : forall (A:Class),
  A :<=: On -> A :<>: :0: -> Class.Ordinal.Core.Ordinal :I(A).
Proof.
  intros A H1 H2. apply TransitiveInclIsOrdinal with On.
  - apply OnIsOrdinal.
  - apply IsTransitive. assumption.
  - apply IsIncl; assumption.
Qed.

Proposition IsLowerBound : forall (A:Class),
  A :<=: On     ->
  A :<>: :0:    ->
  forall a, A a -> :I(A) :<=: toClass a.
Proof.
  intros A H1 H2 a H3 x H4. apply H4. assumption.
Qed.

Proposition IsLargest : forall (A:Class) (a:U),
  A :<=: On                     ->
  A :<>: :0:                    ->
  (forall b, A b  -> a :<=: b)  ->
  toClass a :<=: :I(A).
Proof.
  intros A a H1 H2 H3 x H4 b H5. apply H3; assumption.
Qed.

