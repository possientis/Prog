Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Class.Equiv.



(* Incl P Q <-> forall x, P x -> Q x.                                           *)
Definition Incl : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      All
        (Imp
          (App (Var 2) (Var 0))
          (App (Var 1) (Var 0)))
  |}.



(* forall P Q, equiv P Q <-> Incl P Q /\ Incl Q P.                              *)
Definition Double : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (And
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl") (args [Var 0; Var 1])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R S, equiv P Q -> equiv R S -> Incl P R -> Incl Q S.              *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (Imp
          (IdentT (Name.local "Incl") (args [Var 3; Var 1]))
          (IdentT (Name.local "Incl") (args [Var 2; Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> Incl P R -> Incl Q R.                             *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 2; Var 0]))
        (IdentT (Name.local "Incl") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> Incl R P -> Incl R Q.                             *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 2]))
        (IdentT (Name.local "Incl") (args [Var 0; Var 1])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P, Incl P P.                                                          *)
Definition Refl : DeclP :=
  let concl :=
    IdentT (Name.local "Incl") (args [Var 0; Var 0])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Incl P Q -> Incl Q P -> equiv P Q.                               *)
Definition Anti : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
        (IdentT (Name.local "equiv") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Incl P Q -> Incl Q R -> Incl P R.                              *)
Definition Tran : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl") (args [Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Equiv.exports.

Definition exports : Env := Env.unions
  [ Env.fromListT
    [ (Name.local "Incl", Incl)
    ]
  ; Env.fromListP
    [ (Name.local "Double"       , Double)
    ; (Name.local "EquivCompat"  , EquivCompat)
    ; (Name.local "EquivCompatL" , EquivCompatL)
    ; (Name.local "EquivCompatR" , EquivCompatR)
    ; (Name.local "Refl"         , Refl)
    ; (Name.local "Anti"         , Anti)
    ; (Name.local "Tran"         , Tran)
    ]
  ].

Definition env : Env := Env.union imports exports.
