Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.HasTy.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition empty : Decl :=
  {| para := [];
     res  := TySet;
     body := None |}.

Definition single : Decl :=
  {| para := [TySet];
     res  := TySet;
     body := None |}.

Definition union2 : Decl :=
  {| para := [TySet; TySet];
     res  := TySet;
     body := None |}.

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
Proposition HasTy : HasTy env Ctx.empty Infinity TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyEx, HasTyAnd.
  - apply HasTyElem.
    + apply HasTyIdentT with []. 1: reflexivity.
      apply HasTysNil.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
  - apply HasTyAll, HasTyImp.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyElem.
      * apply HasTyIdentT with [TySet; TySet]. 1: reflexivity.
        apply HasTysCons.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTysCons.
           ++ apply HasTyIdentT with [TySet]. 1: reflexivity.
              apply HasTysCons.
              ** apply (HasTyVar _ _ _ TySet). reflexivity.
              ** apply HasTysNil.
           ++ apply HasTysNil.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
Qed.
