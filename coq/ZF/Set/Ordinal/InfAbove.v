Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.InfAbove.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Inf.
Require Import ZF.Set.Specify.

Export ZF.Notation.InfAbove.

Module SIN := ZF.Set.Inter.
Module SOI := ZF.Set.Ordinal.Inter.

(* The infimum of the set a above b.                                            *)
Definition infAbove (b a:U) : U := inf (a :\: b).

(* Notation "inf(>: b ) a" := (infAbove b a)                                    *)
Global Instance SetInfAbove : InfAbove U := { infAbove := infAbove }.

Proposition Charac : forall (a b x y:U),
  x :< inf(>: b) a  ->
  y :< a            ->
  ~ y :< b          ->
  Ordinal y         ->
  x :< y.
Proof.
  intros a b x y H1 H2 H3 H4. apply Inf.Charac with (a :\: b); try assumption.
  apply Diff.Charac. split; assumption.
Qed.

Proposition CharacRev : forall (a b x:U),
  {{ x :< a :\: b | Ordinal }}  <> :0:                      ->
  (forall y, y :< a -> ~ y :< b -> Ordinal y -> x :< y) ->
  x :< inf(>: b) a.
Proof.
  intros a b x H1 H2. apply Inter.CharacRev. 1: assumption.
  intros y H3. apply Specify.Charac in H3. destruct H3 as [H3 H4].
  apply Diff.Charac in H3. destruct H3 as [H3 H5]. apply H2; assumption.
Qed.

(* The infimum above b of the class is the class of the infimum above b.        *)
Proposition ToClass : forall (a b:U),
  inf(>: b) (toClass a) :~: toClass (inf(>: b) a).
Proof.
  intros a b. apply Equiv.Tran with (Class.Ordinal.Inf.inf (toClass (a :\: b))).
  - apply Inf.EquivCompat, Equiv.Sym, Diff.ToClass.
  - apply Equiv.Sym, Inf.ToClass.
Qed.

(* When ordinals, the infimum of a above b is the intersection of a\b.          *)
Proposition WhenOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  inf(>: b) a = :I(a :\: b).
Proof.
  intros a b H1 H2. unfold Notation.InfAbove.infAbove, infAbove, SetInfAbove.
  unfold infAbove, inf.
  assert ({{ x :< a :\: b | Ordinal }} = a :\: b) as H3. {
    apply Specify.IsA. intros x H3. apply Core.IsOrdinal with a.
    1: assumption. apply Diff.Charac in H3. apply H3. }
  rewrite H3. reflexivity.
Qed.

Proposition IsZero : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: b -> inf(>: b) a = :0:.
Proof.
  intros a b H1 H2 H3.
  rewrite WhenOrdinal; try assumption.
  assert (a :\: b = :0:) as H4. { apply Diff.WhenEmpty. assumption. }
  rewrite H4. apply SIN.WhenEmpty.
Qed.

Proposition IsEqual : forall (a b:U), Ordinal a -> Ordinal b ->
  b :< a -> inf(>: b) a = b.
Proof.
  intros a b H1 H2 H3. rewrite WhenOrdinal; try assumption.
  apply DoubleInclusion. split.
  - apply SOI.IsLowerBound.
    + intros x H4. apply Diff.Charac in H4. destruct H4 as [H4 H5].
      apply Core.IsOrdinal with a; assumption.
    + apply Diff.Charac. split. 1: assumption. apply NoElemLoop1.
  - apply SOI.IsLargest.
    + intros x H4. apply Diff.Charac in H4. destruct H4 as [H4 H5].
      apply Core.IsOrdinal with a; assumption.
    + intros H4. apply Diff.WhenEmpty in H4. apply NoElemLoop1 with b.
      apply H4. assumption.
    + intros c H4. apply Diff.Charac in H4. destruct H4 as [H4 H5].
      assert (Ordinal c) as H6. { apply Core.IsOrdinal with a; assumption. }
      assert (c :< b \/ b :<=: c) as H7. { apply Core.ElemOrIncl; assumption. }
      destruct H7 as [H7|H7]. 1: contradiction. assumption.
Qed.
