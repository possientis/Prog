Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Test.Decl.Class.Equiv.
Require Import ZF.Meta.Test.Decl.Class.Incl.
Require Import ZF.Meta.Test.Decl.Set.Pair.

Import ListNotations.

(* Environment.                                                                 *)

Definition env : Env := Env.unions
  [ Pair.env
  ; Incl.env
  ; Equiv.env
  ].

(* Propositions.                                                                *)

(* Proposition Charac : forall a b, forall x, x :< pair a b <-> x = a \/ x = b. *)
Definition Charac : Term :=
  All VarTySet
    (All VarTySet
      (All VarTySet
        (Iff
          (Elem (Var 0) (IdentT "pair" [Var 2; Var 1]))
          (Or
            (Equal (Var 0) (Var 2))
            (Equal (Var 0) (Var 1)))))).

(* Proposition IsInL : forall a b, a :< pair a b.                               *)
Definition IsInL : Term :=
  All VarTySet
    (All VarTySet
      (Elem (Var 1) (IdentT "pair" [Var 1; Var 0]))).

(* Proposition IsInR : forall a b, b :< pair a b.                               *)
Definition IsInR : Term :=
  All VarTySet
    (All VarTySet
      (Elem (Var 0) (IdentT "pair" [Var 1; Var 0]))).

(* Proposition ToClassIncl : forall A a b,                                      *)
(* A a /\ A b <-> Incl (toClass (pair a b)) A.                                  *)
Definition ToClassIncl : Term :=
  All VarTyClass
    (All VarTySet
      (All VarTySet
        (Iff
          (And
            (App (Var 2) (Var 1))
            (App (Var 2) (Var 0)))
          (IdentT "Incl"
            [IdentT "toClass" [IdentT "pair" [Var 1; Var 0]]; Var 2])))).

(* Proposition typing.                                                          *)

(* The characterization of membership in a pair is well sorted.                 *)
Proposition CharacCheck : HasTyT env Ctx.empty Charac TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyIff.
  - apply HasTyElem.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply pairCheckIdent; reflexivity.
  - apply HasTyOr; apply HasTyEqual; apply (HasTyVar _ _ _ TySet); reflexivity.
Qed.

(* The left element belongs to its pair, and it is well sorted.                 *)
Proposition IsInLCheck : HasTyT env Ctx.empty IsInL TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyElem.
  - apply (HasTyVar _ _ _ TySet). reflexivity.
  - apply pairCheckIdent; reflexivity.
Qed.

(* The right element belongs to its pair, and it is well sorted.                *)
Proposition IsInRCheck : HasTyT env Ctx.empty IsInR TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyElem.
  - apply (HasTyVar _ _ _ TySet). reflexivity.
  - apply pairCheckIdent; reflexivity.
Qed.

(* Containment of both elements and class inclusion are well sorted.            *)
Proposition ToClassInclCheck : HasTyT env Ctx.empty ToClassIncl TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyIff.
  - apply HasTyAnd.
    + apply HasTyApp.
      * apply (HasTyVar _ _ _ TyClass). reflexivity.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTyApp.
      * apply (HasTyVar _ _ _ TyClass). reflexivity.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
  - apply HasTyIdentT with (d:=Incl). 1: reflexivity.
    apply HasTyTsCons.
    + apply HasTyIdentT with (d:=toClass). 1: reflexivity.
      apply HasTyTsCons.
      * apply pairCheckIdent; reflexivity.
      * apply HasTyTsNil.
    + apply HasTyTsCons.
      * apply (HasTyVar _ _ _ TyClass). reflexivity.
      * apply HasTyTsNil.
Qed.
