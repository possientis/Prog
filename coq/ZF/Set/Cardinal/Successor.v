Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Cardinal.Hartogs.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Ordinal.

Require Import ZF.Notation.Successor.
Export ZF.Notation.Successor.

Module CEM := ZF.Class.Empty.
Module SCH := ZF.Set.Cardinal.Hartogs.
Module SCN := ZF.Set.Cardinal.Number.

(* The class of cardinal candidates above the cardinal of a.                    *)
Definition successorClass (a:U) : Class := fun b => Cardinal b /\ ((card a) :< b).

(* The successor cardinal of a set.                                             *)
Definition successor (a:U) : U := inf (successorClass a).

(* Notation "a ^:+:" := (successor a)                                           *)
Global Instance SetSuccessor : Successor U := { successor := successor }.

(* The defining class of successor cardinal candidates contains only ordinals.  *)
Proposition IsIncl : forall (a:U),
  successorClass a :<=: Ordinal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1.
  (* Every candidate is a cardinal, hence an ordinal.                           *)
  destruct H1 as [H1 H2]. apply SCN.CardIsOrd. assumption.
Qed.

(* There is a cardinal strictly above the cardinal of a.                        *)
Proposition HasElem : forall (a:U),
  successorClass a :<>: :0:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a.
  (* Hartogs' number is a cardinal strictly above the cardinal of a.            *)
  apply CEM.HasElem. exists (hartogs a). unfold successorClass. split.
  - apply SCH.IsCardinal.
  - apply SCH.IsMore.
Qed.

(* The successor cardinal is itself a candidate above the cardinal of a.        *)
Proposition Charac : forall (a:U),
  Cardinal (a^:+:) /\ ((card a) :< a^:+:).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a.
  (* The infimum of a non-empty ordinal class belongs to that class.            *)
  apply (InfOfClass.IsIn (successorClass a)).
  - apply IsIncl.
  - apply HasElem.
Qed.

(* The successor cardinal is a cardinal number.                                 *)
Proposition IsCardinal : forall (a:U), Cardinal (a^:+:).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a. apply Charac.
Qed.

(* The cardinal of a is below its successor cardinal.                           *)
Proposition IsMore : forall (a:U), (card a) :< a^:+:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a. apply Charac.
Qed.
