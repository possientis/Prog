Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.HasTy.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Test.Decl.Class.Equiv.

Import ListNotations.

(* Propositions.                                                                *)

(* Proposition Refl : forall (P:Class), equiv P P.                              *)
Definition Refl : Term :=
  All VarTyClass
    (IdentT "equiv" [Var 0; Var 0]).

(* Proposition EquivCompat : forall A B C D,                                    *)
(* equiv A C -> equiv B D -> equiv A B -> equiv C D.                            *)
Definition EquivCompat : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (All VarTyClass
          (Imp
            (IdentT "equiv" [Var 3; Var 1])
            (Imp
              (IdentT "equiv" [Var 2; Var 0])
              (Imp
                (IdentT "equiv" [Var 3; Var 2])
                (IdentT "equiv" [Var 1; Var 0]))))))).

(* Proposition EquivCompatL : forall A B C,                                     *)
(* equiv A C -> equiv A B -> equiv C B.                                         *)
Definition EquivCompatL : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (IdentT "equiv" [Var 2; Var 0])
          (Imp
            (IdentT "equiv" [Var 2; Var 1])
            (IdentT "equiv" [Var 0; Var 1]))))).

(* Proposition EquivCompatR : forall A B C,                                     *)
(* equiv B C -> equiv A B -> equiv A C.                                         *)
Definition EquivCompatR : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (IdentT "equiv" [Var 1; Var 0])
          (Imp
            (IdentT "equiv" [Var 2; Var 1])
            (IdentT "equiv" [Var 2; Var 0]))))).

(* Proposition Sym : forall P Q, equiv P Q -> equiv Q P.                        *)
Definition Sym : Term :=
  All VarTyClass
    (All VarTyClass
      (Imp
        (IdentT "equiv" [Var 1; Var 0])
        (IdentT "equiv" [Var 0; Var 1]))).

(* Proposition Tran : forall P Q R,                                             *)
(* equiv P Q -> equiv Q R -> equiv P R.                                         *)
Definition Tran : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (IdentT "equiv" [Var 2; Var 1])
          (Imp
            (IdentT "equiv" [Var 1; Var 0])
            (IdentT "equiv" [Var 2; Var 0]))))).

(* Proposition NotSym : forall P Q, ~ equiv P Q -> ~ equiv Q P.                 *)
Definition NotSym : Term :=
  All VarTyClass
    (All VarTyClass
      (Imp
        (Not (IdentT "equiv" [Var 1; Var 0]))
        (Not (IdentT "equiv" [Var 0; Var 1])))).

(* Proposition EqualToClass : forall a b,                                       *)
(* a = b <-> equiv (toClass a) (toClass b).                                     *)
Definition EqualToClass : Term :=
  All VarTySet
    (All VarTySet
      (Iff
        (Equal (Var 1) (Var 0))
        (IdentT "equiv"
          [IdentT "toClass" [Var 1]; IdentT "toClass" [Var 0]]))).

(* Proposition NotEqualToClass : forall a b,                                    *)
(* a <> b <-> ~ equiv (toClass a) (toClass b).                                  *)
Definition NotEqualToClass : Term :=
  All VarTySet
    (All VarTySet
      (Iff
        (NotEq (Var 1) (Var 0))
        (Not
          (IdentT "equiv"
            [IdentT "toClass" [Var 1]; IdentT "toClass" [Var 0]])))).

(* Proposition NotCompat : forall P Q R S,                                      *)
(* equiv P Q -> equiv R S -> ~ equiv P R -> ~ equiv Q S.                        *)
Definition NotCompat : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (All VarTyClass
          (Imp
            (IdentT "equiv" [Var 3; Var 2])
            (Imp
              (IdentT "equiv" [Var 1; Var 0])
              (Imp
                (Not (IdentT "equiv" [Var 3; Var 1]))
                (Not (IdentT "equiv" [Var 2; Var 0])))))))).

(* Proposition NotCompatL : forall P Q R,                                       *)
(* equiv P Q -> ~ equiv P R -> ~ equiv Q R.                                     *)
Definition NotCompatL : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (IdentT "equiv" [Var 2; Var 1])
          (Imp
            (Not (IdentT "equiv" [Var 2; Var 0]))
            (Not (IdentT "equiv" [Var 1; Var 0])))))).

(* Proposition NotCompatR : forall P Q R,                                       *)
(* equiv P Q -> ~ equiv R P -> ~ equiv R Q.                                     *)
Definition NotCompatR : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (IdentT "equiv" [Var 2; Var 1])
          (Imp
            (Not (IdentT "equiv" [Var 0; Var 2]))
            (Not (IdentT "equiv" [Var 0; Var 1])))))).

(* Proposition typing.                                                          *)

(* The reflexivity proposition is well sorted using equivalence.                *)
Proposition ReflCheck : HasTy env Ctx.empty Refl TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll.
  apply HasTyIdentT with [TyClass; TyClass]. 1: reflexivity.
  apply HasTysCons.
  - apply (HasTyVar _ _ _ TyClass). reflexivity.
  - apply HasTysCons.
    + apply (HasTyVar _ _ _ TyClass). reflexivity.
    + apply HasTysNil.
Qed.

(* Equivalence compatibility is a well-sorted proposition.                      *)
Proposition EquivCompatCheck : HasTy env Ctx.empty EquivCompat TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyImp.
    + apply equivCheckIdent; reflexivity.
    + apply HasTyImp.
      * apply equivCheckIdent; reflexivity.
      * apply equivCheckIdent; reflexivity.
Qed.

(* Left compatibility of equivalence is a well-sorted proposition.              *)
Proposition EquivCompatLCheck : HasTy env Ctx.empty EquivCompatL TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyImp; apply equivCheckIdent; reflexivity.
Qed.

(* Right compatibility of equivalence is a well-sorted proposition.             *)
Proposition EquivCompatRCheck : HasTy env Ctx.empty EquivCompatR TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyImp; apply equivCheckIdent; reflexivity.
Qed.

(* Symmetry of equivalence is a well-sorted proposition.                        *)
Proposition SymCheck : HasTy env Ctx.empty Sym TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyImp; apply equivCheckIdent; reflexivity.
Qed.

(* Transitivity of equivalence is a well-sorted proposition.                    *)
Proposition TranCheck : HasTy env Ctx.empty Tran TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyImp; apply equivCheckIdent; reflexivity.
Qed.

(* Symmetry of non-equivalence is a well-sorted proposition.                    *)
Proposition NotSymCheck : HasTy env Ctx.empty NotSym TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyImp; apply notEquivCheckIdent; reflexivity.
Qed.

(* Equality of sets and equivalence of their classes is well sorted.            *)
Proposition EqualToClassCheck : HasTy env Ctx.empty EqualToClass TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyIff.
  - apply HasTyEqual; apply (HasTyVar _ _ _ TySet); reflexivity.
  - apply HasTyIdentT with [TyClass; TyClass]. 1: reflexivity.
    apply HasTysCons.
    + apply toClassCheckIdent; reflexivity.
    + apply HasTysCons.
      * apply toClassCheckIdent; reflexivity.
      * apply HasTysNil.
Qed.

(* Inequality of sets and non-equivalence of their classes is well sorted.      *)
Proposition NotEqualToClassCheck :
  HasTy env Ctx.empty NotEqualToClass TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyIff.
  - apply HasTyNotEq; apply (HasTyVar _ _ _ TySet); reflexivity.
  - apply HasTyNot.
    apply HasTyIdentT with [TyClass; TyClass]. 1: reflexivity.
    apply HasTysCons.
    + apply toClassCheckIdent; reflexivity.
    + apply HasTysCons.
      * apply toClassCheckIdent; reflexivity.
      * apply HasTysNil.
Qed.

(* Non-equivalence is compatible with equivalence.                              *)
Proposition NotCompatCheck : HasTy env Ctx.empty NotCompat TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyImp.
    + apply equivCheckIdent; reflexivity.
    + apply HasTyImp.
      * apply notEquivCheckIdent; reflexivity.
      * apply notEquivCheckIdent; reflexivity.
Qed.

(* Non-equivalence is left-compatible with equivalence.                         *)
Proposition NotCompatLCheck : HasTy env Ctx.empty NotCompatL TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyImp; apply notEquivCheckIdent; reflexivity.
Qed.

(* Non-equivalence is right-compatible with equivalence.                        *)
Proposition NotCompatRCheck : HasTy env Ctx.empty NotCompatR TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivCheckIdent; reflexivity.
  - apply HasTyImp; apply notEquivCheckIdent; reflexivity.
Qed.
