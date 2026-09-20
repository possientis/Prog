Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Relation.Eval.
Require Import ZF.Meta.Decl.Set.Relation.FunctionOn.

(* forall a, exists f, FunctionOn f a /\ forall x, x :< a ->                    *)
(* x <> empty -> eval f x :< x.                                                 *)
Definition Choice : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      All
        (Ex
          (And
            (IdentT (Name.local "FunctionOn") (args [Var 0; Var 1]))
            (All
              (Imp
                (Elem (Var 0) (Var 2))
                (Imp
                  (NotEq (Var 0) (IdentT (Name.local "empty") (args [])))
                  (Elem
                    (IdentT (Name.qualified "Eval" "eval") (args [Var 1; Var 0]))
                    (Var 0)))))))
  |}.

Definition imports : Env := Env.unions
  [ Env.unqualify FunctionOn.exports
  ; Env.unqualify Empty.exports
  ; Env.qualifyAs "Eval" Eval.exports
  ].

Definition exports : Env := Env.fromListT
  [ (Name.local "Choice", Choice)
  ].

Definition env : Env := Env.union imports exports.


