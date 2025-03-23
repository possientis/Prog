Require Import ZF.Class.
Require Import ZF.Class.E.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Founded.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Minimal.
Require Import ZF.Class.Total.
Require Import ZF.Class.Tr.
Require Import ZF.Class.V.
Require Import ZF.Class.WellFounded.
Require Import ZF.Class.WellFoundedWellOrd.
Require Import ZF.Class.WellOrdering.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Predicate defining an ordinal class.                                         *)
Definition Ord (A:Class) : Prop := Tr A /\ forall x y,
  A x -> A y -> x = y \/ x :< y \/ y :< x.

(* E is a total order on every ordinal class.                                   *)
Proposition EIsTotalOnOrdinals : forall (A:Class),
  Ord A -> Total E A.
Proof.
  intros A [H1 H2] x y H3 H4. specialize (H2 x y H3 H4). destruct H2 as [H2|[H2|H2]].
  - subst. left. reflexivity.
  - right. left. apply ECharac2. assumption.
  - right. right. apply ECharac2. assumption.
Qed.

(* E is a well-ordering on every ordinal class.                                 *)
Proposition EWellOrdersOrdinals : forall (A:Class),
  Ord A -> WellOrdering E A.
Proof.
  intros A H1. split.
  - apply FoundedIncl with V.
    + apply EIsFoundedOnV.
    + apply VIsSuperClass.
  - apply EIsTotalOnOrdinals. assumption.
Qed.

(* Every non-empty sub-class of an ordinal class has an E-minimal element.      *)
Proposition HasEMinimal : forall (A B:Class),
  Ord A       ->
  B :<=: A    ->
  B :<>: :0:  ->
  exists x, B x /\ B :/\: toClass x :~: :0:.
Proof.
  intros A B H1 H2 H3.
  assert (exists x, Minimal E B x) as H4. { apply HasMinimal with A;
    try assumption. split.
    - apply WellFoundedIncl with V. apply EIsWellFoundedOnV.
      apply VIsSuperClass.
    - apply EWellOrdersOrdinals. assumption. }
  destruct H4 as [x H4]. exists x. apply MinimalEA. assumption.
Qed.
