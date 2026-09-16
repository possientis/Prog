Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

(* Exists A <-> exists x, A x.                                                  *)
Definition Exists : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyProp
  ;  bodyT := Ex (App (Var 1) (Var 0))
  |}.

(* Unique A <-> forall a b, A a -> A b -> a = b.                                *)
Definition Unique : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      All
        (All
          (Imp
            (App (Var 2) (Var 1))
            (Imp
              (App (Var 2) (Var 0))
              (Syntax.Equal (Var 1) (Var 0)))))
  |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ (Name.local "Exists", Exists)
  ; (Name.local "Unique", Unique)
  ].

Definition env : Env := Env.union imports exports.
