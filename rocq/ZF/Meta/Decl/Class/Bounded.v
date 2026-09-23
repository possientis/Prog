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

Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Small.

(* Bounded A <-> exists a, forall x, A x -> x :< a.                             *)
Definition Bounded : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      Ex
        (All
          (Imp
            (App (Var 2) (Var 0))
            (Elem (Var 0) (Var 1))))
  |}.

(* forall A, Bounded A iff Small A.                                             *)
Definition IsSmall : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Bounded") (args [Var 0]))
      (IdentT (Name.local "Small") (args [Var 0]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify Small.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Bounded", Bounded)
      ]
  ; Env.fromListP
      [ (Name.local "IsSmall", IsSmall)
      ]
  ].

Definition env : Env := Env.union imports exports.
