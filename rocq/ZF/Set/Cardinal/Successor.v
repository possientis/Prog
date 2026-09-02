Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Cardinal.Hartogs.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Cardinal.WellOrderable.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Successor.
Export ZF.Notation.Successor.

Module CEM := ZF.Class.Empty.


(* The class of ordinals whose cardinal is above the cardinal of a set.         *)
Definition Above (a:U) : Class := fun b => Ordinal b /\ card a :< card b.

(* The successor cardinal of a set.                                             *)
Definition successor (a:U) : U := inf (Above a).

(* Notation "a ^:+:" := (successor a)                                           *)
Global Instance SetSuccessor : Successor U := { successor := successor }.

(* The successor cardinal is an ordinal.                                        *)
Proposition IsOrdinal : forall (a:U), Ordinal a^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a. apply InfOfClass.IsOrdinal.
Qed.

(* The class of ordinals above a set's cardinal contains only ordinals.         *)
Proposition IsIncl : forall (a:U), Above a :<=: Ordinal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1.
  (* Every member of the class carries the ordinal condition explicitly.        *)
  apply H1.
Qed.

(* There is a cardinal strictly above the cardinal of a set.                    *)
Proposition HasElem : forall (a:U), Above a :<>: :0:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a.
  (* Hartogs' number is an ordinal whose cardinal is strictly larger.           *)
  apply CEM.HasElem. exists (hartogs a). split.
  - apply Hartogs.IsOrdinal.
  - rewrite Hartogs.Card. apply Hartogs.IsMore.
Qed.

(* The successor cardinal is below every ordinal with larger cardinal.          *)
Proposition IsLowerBound : forall (a b:U),
  Ordinal b         ->
  card a :< card b  ->
  a^:+: :<=: b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2.
  (* This is the lower-bound property of the defining infimum.                  *)
  apply (InfOfClass.IsLowerBound (Above a)).
  - apply IsIncl.
  - split; assumption.
Qed.

(* The successor cardinal is below every larger cardinal.                       *)
Proposition IsLowerBoundCard : forall (a b:U),
  Ordinal a -> Cardinal b -> a :< b -> a^:+: :<=: b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2 H3.
  (* For an ordinal below a cardinal, cardinal comparison is equivalent.        *)
  assert (card a :< b) as H4. {
    apply Number.CardLess; assumption. }
  (* Since b is a cardinal, the general lower-bound theorem applies.            *)
  assert (b = card b) as H5. { apply Number.WhenCardinal. assumption. }
  rewrite H5 in H4. apply IsLowerBound. 2: assumption.
  apply Number.CardIsOrd. assumption.
Qed.

(* Below a limit-indexed Aleph, successor cardinals remain below that Aleph.    *)
Proposition IsLessAleph : forall (a b:U),
  Limit a -> b :< Aleph!a -> b^:+: :< Aleph!a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2.
  assert (Ordinal a) as G1. { apply H1. }
  assert (Ordinal Aleph!a) as G2. { apply Aleph.IsOrdinal. assumption. }
  (* Continuity places b below some earlier Aleph value.                        *)
  assert (Aleph!a = :\/:_{a} Aleph) as H3. { apply Aleph.Continuous. assumption. }
  rewrite H3 in H2. apply UnionGenOfClass.Charac in H2.
  destruct H2 as [c [H2 H4]].
  assert (Ordinal c) as G3. { apply Ordinal.IsOrdinal with a; assumption. }
  assert (Ordinal Aleph!c) as G4. { apply Aleph.IsOrdinal. assumption. }
  assert (Cardinal Aleph!c) as G5. { apply Aleph.IsCardinal. assumption. }
  assert (Ordinal b) as G6. { apply Ordinal.IsOrdinal with Aleph!c; assumption. }
  (* The new lower-bound form catches the successor cardinal below Aleph(c).    *)
  assert (b^:+: :<=: Aleph!c) as H5. { apply IsLowerBoundCard; assumption. }
  assert (Aleph!c :< Aleph!a) as H6. { apply Aleph.ElemCompat; assumption. }
  apply Ordinal.InclElemTran with Aleph!c; try assumption. apply IsOrdinal.
Qed.

(* Every common lower bound is below the successor cardinal.                    *)
Proposition IsLargest : forall (a b:U),
  (forall c, Ordinal c -> card a :< card c -> b :<=: c) ->
  b :<=: a^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1.
  (* This is the largest-lower-bound property of the defining infimum.          *)
  apply (InfOfClass.IsLargest (Above a)).
  - apply IsIncl.
  - apply HasElem.
  - intros c H2. destruct H2 as [H2 H3]. apply H1; assumption.
Qed.

(* The successor cardinal belongs to the class of ordinals with larger card.    *)
Proposition IsIn : forall (a:U), Above a a^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a.
  (* It is least in the non-empty class of ordinals with larger card.           *)
  apply (InfOfClass.IsIn (Above a)).
  - apply IsIncl.
  - apply HasElem.
Qed.

(* The successor cardinal is a cardinal number.                                 *)
Proposition IsCardinal : forall (a:U), Cardinal a^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a.
  (* The successor is an ordinal, and its cardinal is above card(a).            *)
  assert (Above a a^:+:) as H1. { apply IsIn. }
  destruct H1 as [H1 H2].
  assert (forall b, Ordinal b -> a^:+: :~: b -> a^:+: :<=: b) as H3. {
    intros b H3 H4.
    (* Any equipotent ordinal has the same cardinal, hence also lies above a.   *)
    assert (card a^:+: = card b) as H5. { apply Number.WhenEquip. assumption. }
    (* The defining infimum is below every ordinal in the defining class.       *)
    apply IsLowerBound. 1: assumption. rewrite <- H5. assumption. }
  apply Number.Charac. split; assumption.
Qed.

(* The cardinal of a successor cardinal is that successor cardinal.             *)
Proposition Card : forall (a:U), card a^:+: = a^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a.
  (* Since a successor cardinal is a cardinal, taking its cardinal changes      *)
  (* nothing.                                                                   *)
  symmetry. apply Number.WhenCardinal. apply IsCardinal.
Qed.

(* The cardinal of a is below the cardinal of its successor cardinal.           *)
Proposition IsMoreCard : forall (a:U), card a :< card a^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a. apply IsIn.
Qed.

(* The cardinal of a is below its successor cardinal.                           *)
Proposition IsMore : forall (a:U), (card a) :< a^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a.
  (* The successor cardinal is a cardinal, so it equals its own cardinal.       *)
  rewrite <- Card. apply IsMoreCard.
Qed.

(* The successor cardinal of an Aleph is the next Aleph.                        *)
Proposition WhenAleph : forall (a:U), Ordinal a ->
  (Aleph!a)^:+: = Aleph!(succ a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1.
  assert (Ordinal (succ a)) as G1. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal Aleph!a) as G2. { apply Aleph.IsOrdinal. assumption. }
  assert (Ordinal Aleph!(succ a)) as G3. { apply Aleph.IsOrdinal. assumption. }
  assert (Cardinal Aleph!a) as G4. { apply Aleph.IsCardinal. assumption. }
  assert (Cardinal Aleph!(succ a)) as G5. { apply Aleph.IsCardinal. assumption. }
  assert (Ordinal (Aleph!a)^:+:) as G6. { apply IsOrdinal. }
  (* Since Aleph(a) is strictly below the next Aleph, the successor cardinal    *)
  (* of Aleph(a) is bounded by that next cardinal.                              *)
  assert ((Aleph!a)^:+: :<=: Aleph!(succ a)) as H2. {
    assert (Aleph!a :< Aleph!(succ a)) as K1. {
      apply Aleph.ElemCompat; try assumption. apply Succ.IsIn. }
    apply IsLowerBoundCard; assumption. }
  (* If the next Aleph were not below the successor cardinal, the successor     *)
  (* cardinal would be an ordinal strictly below that next Aleph.               *)
  assert (Aleph!(succ a) :<=: (Aleph!a)^:+:) as H3. {
    assert ((Aleph!a)^:+: :< Aleph!(succ a) \/
      Aleph!(succ a) :<=: (Aleph!a)^:+:) as K1. {
        apply Ordinal.ElemOrIncl; assumption. }
    destruct K1 as [K1|K1]. 2: assumption. exfalso.
    (* Anything below the next Aleph has cardinal at most Aleph(a).             *)
    assert (card (Aleph!a)^:+: :<=: Aleph!a) as K2. {
      apply Aleph.CardBelowSucc; assumption. }
    (* But a successor cardinal is a cardinal and lies strictly above Aleph(a). *)
    assert (Aleph!a :< (Aleph!a)^:+:) as K4. {
      assert (card (Aleph!a) :< (Aleph!a)^:+:) as L2. { apply IsMore. }
      rewrite Aleph.Card in L2; assumption. }
    rewrite <- Card in K4.
    assert (Aleph!a :< Aleph!a) as K5. { apply K2. assumption. }
    revert K5. apply Foundation.NoLoop1. }
  apply Incl.Double. split; assumption.
Qed.

(* The successor-cardinal operation is monotone on ordinals.                    *)
Proposition InclCompat : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: b -> a^:+: :<=: b^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2 H3.
  (* Inclusion between ordinals gives inclusion between their cardinals.        *)
  assert (WellOrderable b) as H4. { apply WellOrderable.WhenOrdinal. assumption. }
  assert (card a :<=: card b) as H5. { apply Number.InclCompat; assumption. }
  (* The cardinal of a is therefore below the successor cardinal of b.          *)
  assert (card b :< card b^:+:) as H6. { apply IsMoreCard. }
  assert (card a :< card b^:+:) as H7. {
    apply Ordinal.InclElemTran with (card b); try assumption;
    apply Number.IsOrdinal. }
  (* The defining lower-bound property gives the desired monotonicity.          *)
  apply IsLowerBound. 2: assumption. apply IsOrdinal.
Qed.

(* Under choice, the successor-cardinal operation is monotone on sets.          *)
Proposition InclCompatChoice : forall (a b:U), Choice ->
  a :<=: b -> a^:+: :<=: b^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Choice makes b well-orderable, so inclusion gives cardinal inclusion.      *)
  assert (WellOrderable b) as H2. { apply WellOrderable.WithChoice. assumption. }
  assert (card a :<=: card b) as H3. { apply Number.InclCompat; assumption. }
  (* The cardinal of a is therefore below the successor cardinal of b.          *)
  assert (card b :< card b^:+:) as H4. { apply IsMoreCard. }
  assert (card a :< card b^:+:) as H5. {
    apply Ordinal.InclElemTran with (card b); try assumption;
    apply Number.IsOrdinal. }
  (* The defining lower-bound property gives the desired monotonicity.          *)
  apply IsLowerBound. 2: assumption. apply IsOrdinal.
Qed.

(* Every ordinal below the successor has cardinality at most the original.      *)
Proposition WhenLess : forall (a b:U),
  b :< a^:+: -> card b :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1.
  (* A member of the successor cardinal is itself an ordinal.                   *)
  assert (Ordinal a^:+:) as H2. { apply IsOrdinal. }
  assert (Ordinal b) as H3. { apply Ordinal.IsOrdinal with a^:+:; assumption. }
  (* If card(a) were below card(b), then b would be in Above(a).                *)
  assert (card a :< card b \/ card b :<=: card a) as H4. {
    apply Ordinal.ElemOrIncl; apply Number.IsOrdinal. }
  destruct H4 as [H4|H4]. 2: assumption. exfalso.
  (* But then the successor would be below b, contradicting b < successor.      *)
  assert (a^:+: :<=: b) as H6. { apply IsLowerBound; assumption. }
  assert (b :< b) as H7. { apply H6. assumption. }
  revert H7. apply Foundation.NoLoop1.
Qed.
