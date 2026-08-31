Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* forall a b, (forall x, x :< a <-> x :< b) -> a = b                           *)
Definition Extensionality : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      All VarTySet
        (All VarTySet
          (Imp
            (All VarTySet
              (Iff (Elem (Var 0) (Var 2))
                   (Elem (Var 0) (Var 1))))
            (Equal (Var 1) (Var 0))))
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ ("Extensionality"%string, Extensionality)
  ].

Definition env : Env := Env.union imports exports.
