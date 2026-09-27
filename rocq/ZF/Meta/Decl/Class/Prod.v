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

Require Import ZF.Meta.Decl.Class.Bounded.
Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Proper.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Relation.
Require Import ZF.Meta.Decl.Class.Relation.Switch.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Pair.
Require Import ZF.Meta.Decl.Set.Power.
Require Import ZF.Meta.Decl.Set.Single.
Require Import ZF.Meta.Decl.Set.Union2.

(* prod P Q x <-> exists y z, x = (y,z) /\ P y /\ Q z.                          *)
Definition prod : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (Ex
            (And
              (SyntaxT.Equal
                (Var 2)
                (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
              (And
                (App (Var 4) (Var 1))
                (App (Var 3) (Var 0))))))
  |}.

(* forall P Q y z, prod P Q :(y,z): <-> P y /\ Q z.                             *)
Definition Charac2 : DeclP :=
  let concl :=
    Iff
      (App
        (IdentT (Name.local "prod") (args [Var 3; Var 2]))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (And
        (App (Var 3) (Var 1))
        (App (Var 2) (Var 0)))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R S, equiv P Q -> equiv R S -> equiv (prod P R) (prod Q S).       *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "prod") (args [Var 3; Var 1])
            ; IdentT (Name.local "prod") (args [Var 2; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> equiv (prod P R) (prod Q R).                      *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "prod") (args [Var 2; Var 0])
          ; IdentT (Name.local "prod") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> equiv (prod R P) (prod R Q).                      *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "prod") (args [Var 0; Var 2])
          ; IdentT (Name.local "prod") (args [Var 0; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R S, Incl P Q -> Incl R S -> Incl (prod P R) (prod Q S).          *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl")
          (args
            [ IdentT (Name.local "prod") (args [Var 3; Var 1])
            ; IdentT (Name.local "prod") (args [Var 2; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Incl P Q -> Incl (prod P R) (prod Q R).                        *)
Definition InclCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "prod") (args [Var 2; Var 0])
          ; IdentT (Name.local "prod") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Incl P Q -> Incl (prod R P) (prod R Q).                        *)
Definition InclCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "prod") (args [Var 0; Var 2])
          ; IdentT (Name.local "prod") (args [Var 0; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Relation F -> Incl F (prod (domain F) (image F (domain F))).       *)
Definition IsInclRel : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Relation") (args [Var 0]))
      (IdentT (Name.local "Incl")
        (args
          [ Var 0
          ; IdentT (Name.local "prod")
              (args
                [ IdentT (Name.local "domain") (args [Var 0])
                ; IdentT (Name.local "image")
                    (args
                      [ Var 0
                      ; IdentT (Name.local "domain") (args [Var 0])
                      ])
                ])
          ]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, Relation F -> domain F ~ A -> range F <= B -> F <= A x B.      *)
Definition IsInclFun : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Relation") (args [Var 2]))
      (Imp
        (IdentT (Name.local "equiv")
          (args [IdentT (Name.local "domain") (args [Var 2]); Var 1]))
        (Imp
          (IdentT (Name.local "Incl")
            (args [IdentT (Name.local "range") (args [Var 2]); Var 0]))
          (IdentT (Name.local "Incl")
            (args [Var 2; IdentT (Name.local "prod") (args [Var 1; Var 0])]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Small P -> Small Q -> Small (prod P Q).                          *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "prod") (args [Var 1; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, equiv (image Switch (prod P Q)) (prod Q P).                      *)
Definition ImageUnderSwitch : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "image")
            (args
              [ IdentT (Name.local "Switch") (args [])
              ; IdentT (Name.local "prod") (args [Var 1; Var 0])
              ])
        ; IdentT (Name.local "prod") (args [Var 0; Var 1])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Small (prod P Q) -> Small (prod Q P).                            *)
Definition IsSmallComm : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "prod") (args [Var 1; Var 0])]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "prod") (args [Var 0; Var 1])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Proper P -> not equiv Q empty -> Proper (prod P Q).              *)
Definition IsProper : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Proper") (args [Var 1]))
      (Imp
        (Not
          (IdentT (Name.local "equiv")
            (args [Var 0; IdentT (Name.local "empty") (args [])])))
        (IdentT (Name.local "Proper")
          (args [IdentT (Name.local "prod") (args [Var 1; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P, Proper P -> Proper (prod P P).                                     *)
Definition SquareIsProper : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Proper") (args [Var 0]))
      (IdentT (Name.local "Proper")
        (args [IdentT (Name.local "prod") (args [Var 0; Var 0])]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P1 P2 Q1 Q2, inter2 products is product of inter2s.                   *)
Definition Inter2 : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "inter2")
            (args
              [ IdentT (Name.local "prod") (args [Var 3; Var 1])
              ; IdentT (Name.local "prod") (args [Var 2; Var 0])
              ])
        ; IdentT (Name.local "prod")
            (args
              [ IdentT (Name.local "inter2") (args [Var 3; Var 2])
              ; IdentT (Name.local "inter2") (args [Var 1; Var 0])
              ])
        ])
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Bounded.exports
  ; Env.unqualify Class.Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Proper.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify Relation.exports
  ; Env.unqualify Switch.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify Pair.exports
  ; Env.unqualify Power.exports
  ; Env.unqualify Single.exports
  ; Env.unqualify Union2.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "prod", prod)
      ]
  ; Env.fromListP
      [ (Name.local "Charac2"         , Charac2)
      ; (Name.local "EquivCompat"     , EquivCompat)
      ; (Name.local "EquivCompatL"    , EquivCompatL)
      ; (Name.local "EquivCompatR"    , EquivCompatR)
      ; (Name.local "InclCompat"      , InclCompat)
      ; (Name.local "InclCompatL"     , InclCompatL)
      ; (Name.local "InclCompatR"     , InclCompatR)
      ; (Name.local "IsInclRel"       , IsInclRel)
      ; (Name.local "IsInclFun"       , IsInclFun)
      ; (Name.local "IsSmall"         , IsSmall)
      ; (Name.local "ImageUnderSwitch", ImageUnderSwitch)
      ; (Name.local "IsSmallComm"     , IsSmallComm)
      ; (Name.local "IsProper"        , IsProper)
      ; (Name.local "SquareIsProper"  , SquareIsProper)
      ; (Name.local "Inter2"          , Inter2)
      ]
  ].

Definition env : Env := Env.union imports exports.
