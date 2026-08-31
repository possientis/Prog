Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Inter2.

(* forall a, a <> empty -> exists x, x :< a /\ inter2 x a = empty               *)
Definition Foundation : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      All VarTySet
        (Imp
          (NotEq (Var 0) (IdentT "empty" []))
          (Ex VarTySet
            (And
              (Elem (Var 0) (Var 1))
              (Equal
                (IdentT "inter2" [Var 0; Var 1])
                (IdentT "empty" [])))))
  |}.

Definition imports : Env := Env.unions
  [ Empty.exports
  ; Inter2.exports
  ].

Definition exports : Env := Env.fromListT
  [ ("Foundation"%string, Foundation)
  ].

Definition env : Env := Env.union imports exports.
