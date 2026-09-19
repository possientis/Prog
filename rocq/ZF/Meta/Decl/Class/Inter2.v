Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Specification.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* inter2 P Q x <-> P x /\ Q x.                                                 *)
Definition inter2 : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (And
          (App (Var 2) (Var 0))
          (App (Var 1) (Var 0)))
  |}.

(* forall P Q R S, equiv P Q -> equiv R S -> equiv (P /\ R) (Q /\ S).           *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "inter2") (args [Var 3; Var 1])
            ; IdentT (Name.local "inter2") (args [Var 2; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> equiv (P /\ R) (Q /\ R).                          *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "inter2") (args [Var 2; Var 0])
          ; IdentT (Name.local "inter2") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> equiv (R /\ P) (R /\ Q).                          *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "inter2") (args [Var 0; Var 2])
          ; IdentT (Name.local "inter2") (args [Var 0; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R S, Incl P Q -> Incl R S -> Incl (P /\ R) (Q /\ S).              *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl")
          (args
            [ IdentT (Name.local "inter2") (args [Var 3; Var 1])
            ; IdentT (Name.local "inter2") (args [Var 2; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Incl P Q -> Incl (P /\ R) (Q /\ R).                            *)
Definition InclCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "inter2") (args [Var 2; Var 0])
          ; IdentT (Name.local "inter2") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Incl P Q -> Incl (R /\ P) (R /\ Q).                            *)
Definition InclCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "inter2") (args [Var 0; Var 2])
          ; IdentT (Name.local "inter2") (args [Var 0; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, equiv (P /\ Q) (Q /\ P).                                         *)
Definition Comm : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "inter2") (args [Var 1; Var 0])
        ; IdentT (Name.local "inter2") (args [Var 0; Var 1])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Incl (P /\ Q) P.                                                 *)
Definition IsInclL : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [IdentT (Name.local "inter2") (args [Var 1; Var 0]); Var 1])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Incl (P /\ Q) Q.                                                 *)
Definition IsInclR : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [IdentT (Name.local "inter2") (args [Var 1; Var 0]); Var 0])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Small P -> Small (P /\ Q).                                       *)
Definition IsSmallL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 1]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "inter2") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Small Q -> Small (P /\ Q).                                       *)
Definition IsSmallR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 0]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "inter2") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Incl R P -> Incl R Q -> Incl R (P /\ Q).                       *)
Definition IsIncl : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 0; Var 2]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
        (IdentT (Name.local "Incl")
          (args
            [ Var 0
            ; IdentT (Name.local "inter2") (args [Var 2; Var 1])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Incl P Q <-> equiv (P /\ Q) P.                                   *)
Definition WhenInclL : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args [IdentT (Name.local "inter2") (args [Var 1; Var 0]); Var 1]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Incl Q P <-> equiv (P /\ Q) Q.                                   *)
Definition WhenInclR : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
      (IdentT (Name.local "equiv")
        (args [IdentT (Name.local "inter2") (args [Var 1; Var 0]); Var 0]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F P Q, Incl (image F (P /\ Q)) (image F P /\ image F Q).              *)
Definition Image : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args
        [ IdentT (Name.local "image")
            (args
              [ Var 2
              ; IdentT (Name.local "inter2") (args [Var 1; Var 0])
              ])
        ; IdentT (Name.local "inter2")
            (args
              [ IdentT (Name.local "image") (args [Var 2; Var 1])
              ; IdentT (Name.local "image") (args [Var 2; Var 0])
              ])
        ])
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Specification.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "inter2", inter2)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat" , EquivCompat)
      ; (Name.local "EquivCompatL", EquivCompatL)
      ; (Name.local "EquivCompatR", EquivCompatR)
      ; (Name.local "InclCompat"  , InclCompat)
      ; (Name.local "InclCompatL" , InclCompatL)
      ; (Name.local "InclCompatR" , InclCompatR)
      ; (Name.local "Comm"        , Comm)
      ; (Name.local "IsInclL"     , IsInclL)
      ; (Name.local "IsInclR"     , IsInclR)
      ; (Name.local "IsSmallL"    , IsSmallL)
      ; (Name.local "IsSmallR"    , IsSmallR)
      ; (Name.local "IsIncl"      , IsIncl)
      ; (Name.local "WhenInclL"   , WhenInclL)
      ; (Name.local "WhenInclR"   , WhenInclR)
      ; (Name.local "Image"       , Image)
      ]
  ].

Definition env : Env := Env.union imports exports.
