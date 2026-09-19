Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Inter2.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for binary intersection is well sorted.                 *)
Proposition inter2 : CheckT (Inter2.env) Inter2.inter2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckLam, CheckAnd; apply CheckApp; apply CheckVar; reflexivity.
Qed.

(* Proposition typing.                                                          *)
(* Compatibility of binary intersection with equivalence is well sorted.        *)
Proposition EquivCompat : CheckP (Inter2.env) Inter2.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.EquivCompat)
    (conclP Inter2.EquivCompat) TyProp) as H1. {
    unfold Inter2.EquivCompat. cbv [args fromList ctxP conclP paraP].
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsNil.
        * apply CheckTsCons.
          -- apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
            apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsCons.
              ** apply CheckVar. reflexivity.
              ** apply CheckTsNil.
          -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Left compatibility of binary intersection with equivalence is well sorted.   *)
Proposition EquivCompatL : CheckP (Inter2.env) Inter2.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.EquivCompatL)
    (conclP Inter2.EquivCompatL) TyProp) as H1. {
    unfold Inter2.EquivCompatL. cbv [args fromList ctxP conclP paraP].
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckTsCons.
        * apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsNil.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Right compatibility of binary intersection with equivalence is well sorted.  *)
Proposition EquivCompatR : CheckP (Inter2.env) Inter2.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.EquivCompatR)
    (conclP Inter2.EquivCompatR) TyProp) as H1. {
    unfold Inter2.EquivCompatR. cbv [args fromList ctxP conclP paraP].
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckTsCons.
        * apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsNil.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Compatibility of binary intersection with inclusion is well sorted.          *)
Proposition InclCompat : CheckP (Inter2.env) Inter2.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.InclCompat)
    (conclP Inter2.InclCompat) TyProp) as H1. {
    unfold Inter2.InclCompat. cbv [args fromList ctxP conclP paraP].
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsNil.
        * apply CheckTsCons.
          -- apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
            apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsCons.
              ** apply CheckVar. reflexivity.
              ** apply CheckTsNil.
          -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Left compatibility of binary intersection with inclusion is well sorted.     *)
Proposition InclCompatL : CheckP (Inter2.env) Inter2.InclCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.InclCompatL)
    (conclP Inter2.InclCompatL) TyProp) as H1. {
    unfold Inter2.InclCompatL. cbv [args fromList ctxP conclP paraP].
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckTsCons.
        * apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsNil.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Right compatibility of binary intersection with inclusion is well sorted.    *)
Proposition InclCompatR : CheckP (Inter2.env) Inter2.InclCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.InclCompatR)
    (conclP Inter2.InclCompatR) TyProp) as H1. {
    unfold Inter2.InclCompatR. cbv [args fromList ctxP conclP paraP].
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckTsCons.
        * apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsNil.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Commutativity of binary intersection is well sorted.                         *)
Proposition Comm : CheckP (Inter2.env) Inter2.Comm.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.Comm)
    (conclP Inter2.Comm) TyProp) as H1. {
    unfold Inter2.Comm. cbv [args fromList ctxP conclP paraP].
    apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
    apply CheckTsCons.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckTsCons.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The left inclusion property of binary intersection is well sorted.           *)
Proposition IsInclL : CheckP (Inter2.env) Inter2.IsInclL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.IsInclL)
    (conclP Inter2.IsInclL) TyProp) as H1. {
    unfold Inter2.IsInclL. cbv [args fromList ctxP conclP paraP].
    apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
    apply CheckTsCons.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The right inclusion property of binary intersection is well sorted.          *)
Proposition IsInclR : CheckP (Inter2.env) Inter2.IsInclR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.IsInclR)
    (conclP Inter2.IsInclR) TyProp) as H1. {
    unfold Inter2.IsInclR. cbv [args fromList ctxP conclP paraP].
    apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
    apply CheckTsCons.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Left smallness of binary intersection is well sorted.                        *)
Proposition IsSmallL : CheckP (Inter2.env) Inter2.IsSmallL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.IsSmallL)
    (conclP Inter2.IsSmallL) TyProp) as H1. {
    unfold Inter2.IsSmallL. cbv [args fromList ctxP conclP paraP].
    apply CheckImp.
    - apply CheckIdentT with [TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil.
    - apply CheckIdentT with [TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Right smallness of binary intersection is well sorted.                       *)
Proposition IsSmallR : CheckP (Inter2.env) Inter2.IsSmallR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.IsSmallR)
    (conclP Inter2.IsSmallR) TyProp) as H1. {
    unfold Inter2.IsSmallR. cbv [args fromList ctxP conclP paraP].
    apply CheckImp.
    - apply CheckIdentT with [TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil.
    - apply CheckIdentT with [TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The universal property of binary intersection is well sorted.                *)
Proposition IsIncl : CheckP (Inter2.env) Inter2.IsIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.IsIncl)
    (conclP Inter2.IsIncl) TyProp) as H1. {
    unfold Inter2.IsIncl. cbv [args fromList ctxP conclP paraP].
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
            apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsCons.
              ** apply CheckVar. reflexivity.
              ** apply CheckTsNil.
          -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The left inclusion characterization is well sorted.                          *)
Proposition WhenInclL : CheckP (Inter2.env) Inter2.WhenInclL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.WhenInclL)
    (conclP Inter2.WhenInclL) TyProp) as H1. {
    unfold Inter2.WhenInclL. cbv [args fromList ctxP conclP paraP].
    apply CheckIff.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The right inclusion characterization is well sorted.                         *)
Proposition WhenInclR : CheckP (Inter2.env) Inter2.WhenInclR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.WhenInclR)
    (conclP Inter2.WhenInclR) TyProp) as H1. {
    unfold Inter2.WhenInclR. cbv [args fromList ctxP conclP paraP].
    apply CheckIff.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Image inclusion through binary intersection is well sorted.                  *)
Proposition Image : CheckP (Inter2.env) Inter2.Image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Inter2.env) (ctxP Inter2.Image)
    (conclP Inter2.Image) TyProp) as H1. {
    unfold Inter2.Image. cbv [args fromList ctxP conclP paraP].
    apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
    apply CheckTsCons.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsNil.
        * apply CheckTsNil.
    - apply CheckTsCons.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsNil.
        * apply CheckTsCons.
          -- apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
            apply CheckTsCons.
            ++ apply CheckVar. reflexivity.
            ++ apply CheckTsCons.
              ** apply CheckVar. reflexivity.
              ** apply CheckTsNil.
          -- apply CheckTsNil.
      + apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
