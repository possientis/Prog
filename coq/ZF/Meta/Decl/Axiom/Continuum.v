Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Class.Cardinal.Aleph.
Require Import ZF.Meta.Decl.Set.Cardinal.Number.
Require Import ZF.Meta.Decl.Set.Ordinal.Ordinal.
Require Import ZF.Meta.Decl.Set.Ordinal.Succ.
Require Import ZF.Meta.Decl.Set.Power.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

Export ZF.Meta.Decl.Class.Cardinal.Aleph.
Export ZF.Meta.Decl.Set.Cardinal.Number.
Export ZF.Meta.Decl.Set.Ordinal.Ordinal.
Export ZF.Meta.Decl.Set.Ordinal.Succ.
Export ZF.Meta.Decl.Set.Power.
Export ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* forall a, Ordinal a -> card (power (eval Aleph a)) = eval Aleph (succ a)     *)
Definition GCH : DeclT :=
  {| para := []
  ;  res  := TyProp
  ;  body :=
      All VarTySet
        (Imp
          (IdentT "Ordinal" [Var 0])
          (Equal
            (IdentT "card"
              [IdentT "power"
                [IdentT "eval" [IdentT "Aleph" []; Var 0]]])
            (IdentT "eval" [IdentT "Aleph" []; IdentT "succ" [Var 0]])))
  |}.

Definition env : Env := Env.unions
  [ Env.fromListT
    [ ("GCH"%string, GCH)
    ]
  ; Aleph.env
  ; Number.env
  ; Ordinal.env
  ; Succ.env
  ; Power.env
  ; EvalOfClass.env
  ].
