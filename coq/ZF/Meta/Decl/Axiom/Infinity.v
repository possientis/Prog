Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Single.
Require Import ZF.Meta.Decl.Set.Union2.

(* exists a, empty :< a /\ forall x, x :< a -> union2 x (single x) :< a         *)
Definition Infinity : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      Ex VarTySet
        (And
          (Elem (IdentT "empty" []) (Var 0))
          (All VarTySet
            (Imp
              (Elem (Var 0) (Var 1))
              (Elem
                (IdentT "union2" [Var 0; IdentT "single" [Var 0]])
                (Var 1)))))
  |}.

Definition imports : Env := Env.unions
  [ Empty.exports
  ; Single.exports
  ; Union2.exports
  ].

Definition exports : Env := Env.fromListT
  [ ("Infinity"%string, Infinity)
  ].

Definition env : Env := Env.union imports exports.
