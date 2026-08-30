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

Definition single : Decl :=
  {| paraT := [TySet];
     resT  := TySet;
     bodyT := HoleT TySet |}.

Definition union2 : Decl :=
  {| paraT := [TySet; TySet];
     resT  := TySet;
     bodyT := HoleT TySet |}.

Definition env : Env := Env.fromListT
  [ ("empty"%string , empty)
  ; ("single"%string, single)
  ; ("union2"%string, union2)
  ].

(* exists a, empty :< a /\ forall x, x :< a -> union2 x (single x) :< a         *)
Definition Infinity : Term :=
  Ex VarTySet
    (And
      (Elem (IdentT "empty" []) (Var 0))
      (All VarTySet
        (Imp
          (Elem (Var 0) (Var 1))
          (Elem
            (IdentT "union2" [Var 0; IdentT "single" [Var 0]])
            (Var 1))))).

(* The infinity example is a proposition in the local test environment.         *)
Proposition Check : CheckT env Ctx.empty Infinity TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckEx, CheckAnd.
  - apply CheckElem.
    + apply CheckIdentT with []. 1: reflexivity.
      apply CheckTsNil.
    + apply CheckVar. reflexivity.
  - apply CheckAll, CheckImp.
    + apply CheckElem; apply CheckVar; reflexivity.
    + apply CheckElem.
      * apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsCons.
           ++ apply CheckIdentT with [TySet]. 1: reflexivity.
              apply CheckTsCons.
              ** apply CheckVar. reflexivity.
              ** apply CheckTsNil.
           ++ apply CheckTsNil.
      * apply CheckVar. reflexivity.
Qed.
