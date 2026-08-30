Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Class.Cardinal.Aleph.
Require Import ZF.Meta.Decl.Set.Cardinal.Number.
Require Import ZF.Meta.Decl.Set.Ordinal.Natural.
Require Import ZF.Meta.Decl.Set.Ordinal.Omega.
Require Import ZF.Meta.Decl.Set.Ordinal.Ordinal.
Require Import ZF.Meta.Decl.Set.Ordinal.Succ.
Require Import ZF.Meta.Decl.Set.Power.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.


(* The continuum hypothesis says that the continuum is the first uncountable.   *)
Definition CH : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      Equal
        (IdentT "card" [IdentT "power" [IdentT "omega" []]])
        (IdentT "eval" [IdentT "Aleph" []; IdentT "one" []])
  |}.

(* forall a, Ordinal a -> card (power (eval Aleph a)) = eval Aleph (succ a)     *)
Definition GCH : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      All VarTySet
        (Imp
          (IdentT "Ordinal" [Var 0])
          (Equal
            (IdentT "card"
              [IdentT "power"
                [IdentT "eval" [IdentT "Aleph" []; Var 0]]])
            (IdentT "eval" [IdentT "Aleph" []; IdentT "succ" [Var 0]])))
  |}.

(* The generalized continuum hypothesis implies the continuum hypothesis.       *)
Definition WhenGCH : DeclP :=
  let concl :=
    Imp
      (IdentT "GCH" [])
      (IdentT "CH" [])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

Definition imports : Env := Env.unions
  [ Aleph.exports
  ; Number.exports
  ; Natural.exports
  ; Omega.exports
  ; Ordinal.exports
  ; Succ.exports
  ; Power.exports
  ; EvalOfClass.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
    [ ("CH"%string , CH)
    ; ("GCH"%string, GCH)
    ]
  ; Env.fromListP
    [ ("WhenGCH"%string, WhenGCH)
    ]
  ].

Definition env : Env := Env.union imports exports.
