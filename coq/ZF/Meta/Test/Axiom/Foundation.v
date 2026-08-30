Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition empty : Decl :=
  {| paraT := [];
     resT  := TySet;
     bodyT := HoleT TySet |}.

Definition inter : Decl :=
  {| paraT := [TySet; TySet];
     resT  := TySet;
     bodyT := HoleT TySet |}.

Definition env : Env := Env.fromListT
  [ ("empty"%string, empty)
  ; ("inter"%string, inter)
  ].

(* forall a, a <> empty -> exists x, x :< a /\ inter x a = empty                *)
Definition Foundation : Term :=
  All VarTySet
    (Imp
      (NotEq (Var 0) (IdentT "empty" []))
      (Ex VarTySet
        (And
          (Elem (Var 0) (Var 1))
          (Equal
            (IdentT "inter" [Var 0; Var 1])
            (IdentT "empty" []))))).

(* The foundation example is a proposition in the local test environment.       *)
Proposition Check : CheckT env Ctx.empty Foundation TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckImp.
  - apply CheckNotEq.
    + apply CheckVar. reflexivity.
    + apply CheckIdentT with []. 1: reflexivity.
      apply CheckTsNil.
  - apply CheckEx, CheckAnd.
    + apply CheckElem; apply CheckVar; reflexivity.
    + apply CheckEqual.
      * apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsCons.
           ++ apply CheckVar. reflexivity.
           ++ apply CheckTsNil.
      * apply CheckIdentT with []. 1: reflexivity.
        apply CheckTsNil.
Qed.
