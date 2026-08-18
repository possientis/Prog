Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Cardinal.Hartogs.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Ordinal.

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
  assert (hartogs a = card (hartogs a)) as H1. {
    apply Number.WhenCardinal. apply Hartogs.IsCardinal. }
  apply CEM.HasElem. exists (hartogs a). split.
  - apply Hartogs.IsOrdinal.
  - rewrite <- H1. apply Hartogs.IsMore.
Qed.

(* The successor cardinal is below every ordinal with larger cardinal.          *)
Proposition IsLowerBound : forall (a b:U), Above a b -> a^:+: :<=: b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1.
  (* This is the lower-bound property of the defining infimum.                  *)
  apply (InfOfClass.IsLowerBound (Above a)).
  - apply IsIncl.
  - assumption.
Qed.

(* Every common lower bound is below the successor cardinal.                    *)
Proposition IsLargest : forall (a b:U),
  (forall c, Above a c -> b :<=: c) -> b :<=: a^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1.
  (* This is the largest-lower-bound property of the defining infimum.          *)
  apply (InfOfClass.IsLargest (Above a)).
  - apply IsIncl.
  - apply HasElem.
  - assumption.
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
    assert (Above a b) as H6. {
      split. 1: assumption. rewrite <- H5. assumption. }
    (* The defining infimum is below every ordinal in the defining class.       *)
    apply IsLowerBound. assumption. }
  apply Number.Charac. split; assumption.
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
  assert (a^:+: = card a^:+:) as H1. {
    apply Number.WhenCardinal. apply IsCardinal. }
  rewrite H1. apply IsMoreCard.
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
  assert (Above a b) as H5. { split; assumption. }
  (* But then the successor would be below b, contradicting b < successor.      *)
  assert (a^:+: :<=: b) as H6. { apply IsLowerBound. assumption. }
  assert (b :< b) as H7. { apply H6. assumption. }
  revert H7. apply Foundation.NoLoop1.
Qed.
