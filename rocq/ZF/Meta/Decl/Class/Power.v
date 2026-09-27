Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Power.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.Incl.

(* power a x <-> x <= a.                                                        *)
Definition power : DeclT :=
  {| paraT := [TySet]
  ;  resT  := TyClass
  ;  bodyT := Lam (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
  |}.

(* forall a, Small (power a).                                                   *)
Definition IsSmall : DeclP :=
  let concl :=
    IdentT (Name.local "Small")
      (args [IdentT (Name.local "power") (args [Var 0])])
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Power.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify Incl.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "power", power)
      ]
  ; Env.fromListP
      [ (Name.local "IsSmall", IsSmall)
      ]
  ].

Definition env : Env := Env.union imports exports.
