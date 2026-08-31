Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* forall P, forall a, exists b, forall x, x :< b <-> x :< a /\ P x             *)
Definition Specification : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      All VarTyClass
        (All VarTySet
          (Ex VarTySet
            (All VarTySet
              (Iff
                (Elem (Var 0) (Var 1))
                (And
                  (Elem (Var 0) (Var 2))
                  (App (Var 3) (Var 0)))))))
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ ("Specification"%string, Specification)
  ].

Definition env : Env := Env.union imports exports.
