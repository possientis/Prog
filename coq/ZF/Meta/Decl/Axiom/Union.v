Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* forall a, exists b, forall x, x :< b <-> exists y, x :< y /\ y :< a          *)
Definition Union : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      All VarTySet
        (Ex VarTySet
          (All VarTySet
            (Iff
              (Elem (Var 0) (Var 1))
              (Ex VarTySet
                (And
                  (Elem (Var 1) (Var 0))
                  (Elem (Var 0) (Var 3)))))))
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ ("Union"%string, Union)
  ].

Definition env : Env := Env.union imports exports.
