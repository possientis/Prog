Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* forall a b, exists c, forall x, x :< c <-> x = a \/ x = b                    *)
Definition Pairing : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      All VarTySet
        (All VarTySet
          (Ex VarTySet
            (All VarTySet
              (Iff
                (Elem (Var 0) (Var 1))
                (Or
                  (Equal (Var 0) (Var 3))
                  (Equal (Var 0) (Var 2)))))))
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ ("Pairing"%string, Pairing)
  ].

Definition env : Env := Env.union imports exports.
