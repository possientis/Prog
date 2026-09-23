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

Require Import ZF.Meta.Decl.Axiom.Classic.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.

(* Less P Q <-> Incl P Q /\ not equiv P Q.                                      *)
Definition Less : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      And
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (Not (IdentT (Name.local "equiv") (args [Var 1; Var 0])))
  |}.

(* forall P Q R S, equiv P Q -> equiv R S -> Less P R -> Less Q S.              *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (Imp
          (IdentT (Name.local "Less") (args [Var 3; Var 1]))
          (IdentT (Name.local "Less") (args [Var 2; Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> Less P R -> Less Q R.                             *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Less") (args [Var 2; Var 0]))
        (IdentT (Name.local "Less") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> Less R P -> Less R Q.                             *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Less") (args [Var 0; Var 2]))
        (IdentT (Name.local "Less") (args [Var 0; Var 1])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Less P Q iff Incl P Q /\ exists x, Q x /\ not P x.               *)
Definition Exists : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Less") (args [Var 1; Var 0]))
      (And
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (Ex
          (And
            (App (Var 1) (Var 0))
            (Not (App (Var 2) (Var 0))))))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Incl P Q -> Less Q R -> Less P R.                              *)
Definition InclLessTran : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Less") (args [Var 1; Var 0]))
        (IdentT (Name.local "Less") (args [Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Less P Q -> Incl Q R -> Less P R.                              *)
Definition LessInclTran : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Less") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Less") (args [Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Incl P Q iff equiv P Q or Less P Q.                              *)
Definition EquivOrLess : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (Or
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (IdentT (Name.local "Less") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Classic.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Incl.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Less", Less)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat" , EquivCompat)
      ; (Name.local "EquivCompatL", EquivCompatL)
      ; (Name.local "EquivCompatR", EquivCompatR)
      ; (Name.local "Exists"      , Exists)
      ; (Name.local "InclLessTran", InclLessTran)
      ; (Name.local "LessInclTran", LessInclTran)
      ; (Name.local "EquivOrLess" , EquivOrLess)
      ]
  ].

Definition env : Env := Env.union imports exports.
