Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Set.Pair.

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
Proposition CharacCheck : CheckT env Ctx.empty Charac TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckAll, CheckAll, CheckIff.
  - apply CheckElem.
    + apply (CheckVar _ _ _ TySet). reflexivity.
    + apply pairCheckIdent; reflexivity.
  - apply CheckOr; apply CheckEqual; apply (CheckVar _ _ _ TySet); reflexivity.
Qed.

(* The left element belongs to its pair, and it is well sorted.                 *)
Proposition IsInLCheck : CheckT env Ctx.empty IsInL TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckAll, CheckElem.
  - apply (CheckVar _ _ _ TySet). reflexivity.
  - apply pairCheckIdent; reflexivity.
Qed.

(* The right element belongs to its pair, and it is well sorted.                *)
Proposition IsInRCheck : CheckT env Ctx.empty IsInR TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckAll, CheckElem.
  - apply (CheckVar _ _ _ TySet). reflexivity.
  - apply pairCheckIdent; reflexivity.
Qed.

(* Containment of both elements and class inclusion are well sorted.            *)
Proposition ToClassInclCheck : CheckT env Ctx.empty ToClassIncl TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckAll, CheckAll, CheckIff.
  - apply CheckAnd.
    + apply CheckApp.
      * apply (CheckVar _ _ _ TyClass). reflexivity.
      * apply (CheckVar _ _ _ TySet). reflexivity.
    + apply CheckApp.
      * apply (CheckVar _ _ _ TyClass). reflexivity.
      * apply (CheckVar _ _ _ TySet). reflexivity.
  - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckIdentT with [TySet]. 1: reflexivity.
      apply CheckTsCons.
      * apply pairCheckIdent; reflexivity.
      * apply CheckTsNil.
    + apply CheckTsCons.
      * apply (CheckVar _ _ _ TyClass). reflexivity.
      * apply CheckTsNil.
Qed.
