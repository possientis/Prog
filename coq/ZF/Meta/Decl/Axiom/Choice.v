Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Relation.Eval.
Require Import ZF.Meta.Decl.Set.Relation.FunctionOn.

(* forall a,                                                                    *)
(*  exists f, FunctionOn f a /\ forall x, x :< a -> x <> empty -> eval f x :< x *)
Definition Choice : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      All VarTySet
        (Ex VarTySet
          (And
            (IdentT "FunctionOn" [Var 0; Var 1])
            (All VarTySet
              (Imp
                (Elem (Var 0) (Var 2))
                (Imp
                  (NotEq (Var 0) (IdentT "empty" []))
                  (Elem (IdentT "eval" [Var 1; Var 0]) (Var 0)))))))
  |}.

Definition imports : Env := Env.unions
  [ FunctionOn.exports
  ; Empty.exports
  ; Eval.exports
  ].

Definition exports : Env := Env.fromListT
  [ ("Choice"%string, Choice)
  ].

Definition env : Env := Env.union imports exports.


