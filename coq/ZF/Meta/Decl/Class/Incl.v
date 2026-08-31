Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

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
      (IdentT "equiv" [Var 1; Var 0])
      (And
        (IdentT "Incl" [Var 1; Var 0])
        (IdentT "Incl" [Var 0; Var 1]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R S, equiv P Q -> equiv R S -> Incl P R -> Incl Q S.              *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT "equiv" [Var 3; Var 2])
      (Imp
        (IdentT "equiv" [Var 1; Var 0])
        (Imp
          (IdentT "Incl" [Var 3; Var 1])
          (IdentT "Incl" [Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> Incl P R -> Incl Q R.                             *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT "equiv" [Var 2; Var 1])
      (Imp
        (IdentT "Incl" [Var 2; Var 0])
        (IdentT "Incl" [Var 1; Var 0]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> Incl R P -> Incl R Q.                             *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT "equiv" [Var 2; Var 1])
      (Imp
        (IdentT "Incl" [Var 0; Var 2])
        (IdentT "Incl" [Var 0; Var 1]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P, Incl P P.                                                          *)
Definition Refl : DeclP :=
  let concl :=
    IdentT "Incl" [Var 0; Var 0]
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Incl P Q -> Incl Q P -> equiv P Q.                               *)
Definition Anti : DeclP :=
  let concl :=
    Imp
      (IdentT "Incl" [Var 1; Var 0])
      (Imp
        (IdentT "Incl" [Var 0; Var 1])
        (IdentT "equiv" [Var 1; Var 0]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Incl P Q -> Incl Q R -> Incl P R.                              *)
Definition Tran : DeclP :=
  let concl :=
    Imp
      (IdentT "Incl" [Var 2; Var 1])
      (Imp
        (IdentT "Incl" [Var 1; Var 0])
        (IdentT "Incl" [Var 2; Var 0]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Equiv.exports.

Definition exports : Env := Env.unions
  [ Env.fromListT
    [ ("Incl"%string, Incl)
    ]
  ; Env.fromListP
    [ ("Double"%string       , Double)
    ; ("EquivCompat"%string  , EquivCompat)
    ; ("EquivCompatL"%string , EquivCompatL)
    ; ("EquivCompatR"%string , EquivCompatR)
    ; ("Refl"%string         , Refl)
    ; ("Anti"%string         , Anti)
    ; ("Tran"%string         , Tran)
    ]
  ].

Definition env : Env := Env.union imports exports.
