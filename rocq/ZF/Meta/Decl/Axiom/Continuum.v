Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Class.Cardinal.Aleph.
Require Import ZF.Meta.Decl.Set.Cardinal.Number.
Require Import ZF.Meta.Decl.Set.Ordinal.Natural.
Require Import ZF.Meta.Decl.Set.Ordinal.Omega.
Require Import ZF.Meta.Decl.Set.Ordinal.Ordinal.
Require Import ZF.Meta.Decl.Set.Ordinal.Succ.
Require Import ZF.Meta.Decl.Set.Power.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.


(* CH := card (power omega) = eval Aleph one.                                   *)
Definition CH : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      Equal
        (IdentT (Name.local "card")
          (args [IdentT (Name.local "power")
            (args [IdentT (Name.local "omega") (args [])])]))
        (IdentT EvalOfClass.evalName
          (args [IdentT (Name.local "Aleph") (args []);
           IdentT (Name.local "one") (args [])]))
  |}.

(* forall a, Ordinal a -> card (power (eval Aleph a)) = eval Aleph (succ a)     *)
Definition GCH : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      All
        (Imp
          (IdentT (Name.local "Ordinal") (args [Var 0]))
          (Equal
            (IdentT (Name.local "card")
              (args [IdentT (Name.local "power")
                (args [IdentT EvalOfClass.evalName
                  (args [IdentT (Name.local "Aleph") (args []); Var 0])])]))
            (IdentT EvalOfClass.evalName
              (args [IdentT (Name.local "Aleph") (args []);
               IdentT (Name.local "succ") (args [Var 0])]))))
  |}.

(* GCH -> CH.                                                                   *)
Definition WhenGCH : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "GCH") (args []))
      (IdentT (Name.local "CH") (args []))
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
    [ (Name.local "CH" , CH)
    ; (Name.local "GCH", GCH)
    ]
  ; Env.fromListP
    [ (Name.local "WhenGCH", WhenGCH)
    ]
  ].

Definition env : Env := Env.union imports exports.
