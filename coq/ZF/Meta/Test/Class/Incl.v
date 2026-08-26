Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.HasTyIn.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Test.Decl.Class.Equiv.
Require Import ZF.Meta.Test.Decl.Class.Incl.

Import ListNotations.

(* Environment.                                                                 *)

Definition env : Env := Env.unions
  [ Incl.env
  ; Equiv.env
  ].

(* Propositions.                                                                *)

(* Proposition Double : forall P Q, equiv P Q <-> Incl P Q /\ Incl Q P.         *)
Definition Double : Term :=
  All VarTyClass
    (All VarTyClass
      (Iff
        (Ident "equiv" [Var 1; Var 0])
        (And
          (Ident "Incl" [Var 1; Var 0])
          (Ident "Incl" [Var 0; Var 1])))).

(* Proposition EquivCompat : forall P Q R S,                                    *)
(* equiv P Q -> equiv R S -> Incl P R -> Incl Q S.                              *)
Definition EquivCompat : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (All VarTyClass
          (Imp
            (Ident "equiv" [Var 3; Var 2])
            (Imp
              (Ident "equiv" [Var 1; Var 0])
              (Imp
                (Ident "Incl" [Var 3; Var 1])
                (Ident "Incl" [Var 2; Var 0]))))))).

(* Proposition EquivCompatL : forall P Q R,                                     *)
(* equiv P Q -> Incl P R -> Incl Q R.                                           *)
Definition EquivCompatL : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (Ident "equiv" [Var 2; Var 1])
          (Imp
            (Ident "Incl" [Var 2; Var 0])
            (Ident "Incl" [Var 1; Var 0]))))).

(* Proposition EquivCompatR : forall P Q R,                                     *)
(* equiv P Q -> Incl R P -> Incl R Q.                                           *)
Definition EquivCompatR : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (Ident "equiv" [Var 2; Var 1])
          (Imp
            (Ident "Incl" [Var 0; Var 2])
            (Ident "Incl" [Var 0; Var 1]))))).

(* Proposition Refl : forall (P:Class), Incl P P.                               *)
Definition Refl : Term :=
  All VarTyClass
    (Ident "Incl" [Var 0; Var 0]).

(* Proposition Anti : forall P Q, Incl P Q -> Incl Q P -> equiv P Q.            *)
Definition Anti : Term :=
  All VarTyClass
    (All VarTyClass
      (Imp
        (Ident "Incl" [Var 1; Var 0])
        (Imp
          (Ident "Incl" [Var 0; Var 1])
          (Ident "equiv" [Var 1; Var 0])))).

(* Proposition Tran : forall P Q R, Incl P Q -> Incl Q R -> Incl P R.           *)
Definition Tran : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (Ident "Incl" [Var 2; Var 1])
          (Imp
            (Ident "Incl" [Var 1; Var 0])
            (Ident "Incl" [Var 2; Var 0]))))).

(* Proposition typing.                                                          *)

(* Double inclusion and equivalence form a well-sorted proposition.             *)
Proposition DoubleCheck : HasTyIn env Ctx.empty Double TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyIff.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyAnd; apply InclCheckIdent; reflexivity.
Qed.

(* Compatibility of inclusion with equivalence is well sorted.                  *)
Proposition EquivCompatCheck : HasTyIn env Ctx.empty EquivCompat TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyImp.
    + apply equivCheckIdent; reflexivity.
    + apply HasTyImp.
      * apply InclCheckIdent; reflexivity.
      * apply InclCheckIdent; reflexivity.
Qed.

(* Left compatibility of inclusion with equivalence is well sorted.             *)
Proposition EquivCompatLCheck : HasTyIn env Ctx.empty EquivCompatL TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyImp; apply InclCheckIdent; reflexivity.
Qed.

(* Right compatibility of inclusion with equivalence is well sorted.            *)
Proposition EquivCompatRCheck : HasTyIn env Ctx.empty EquivCompatR TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyImp; apply InclCheckIdent; reflexivity.
Qed.

(* Reflexivity of inclusion is a well-sorted proposition.                       *)
Proposition ReflCheck : HasTyIn env Ctx.empty Refl TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll.
  apply HasTyIdent with (argTys := [TyClass; TyClass]). 1: reflexivity.
  apply HasTysCons.
  - apply (HasTyVar _ _ _ TyClass). reflexivity.
  - apply HasTysCons.
    + apply (HasTyVar _ _ _ TyClass). reflexivity.
    + apply HasTysNil.
Qed.

(* Antisymmetry of inclusion is a well-sorted proposition.                      *)
Proposition AntiCheck : HasTyIn env Ctx.empty Anti TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyImp.
  - apply InclCheckIdent; reflexivity.
  - apply HasTyImp.
    + apply InclCheckIdent; reflexivity.
    + apply equivCheckIdent; reflexivity.
Qed.

(* Transitivity of inclusion is a well-sorted proposition.                      *)
Proposition TranCheck : HasTyIn env Ctx.empty Tran TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply InclCheckIdent; reflexivity.
  - apply HasTyImp; apply InclCheckIdent; reflexivity.
Qed.
