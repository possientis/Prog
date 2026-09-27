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
Require Import ZF.Meta.Decl.Class.Complement.
Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.IsSetOf.
Require Import ZF.Meta.Decl.Class.Less.
Require Import ZF.Meta.Decl.Class.Proper.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Class.Union2.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* diff A B x <-> A x /\ not B x.                                               *)
Definition diff : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      IdentT (Name.local "inter2")
        (args [Var 1; IdentT (Name.local "complement") (args [Var 0])])
  |}.

(* forall A B C D, A ~ C -> B ~ D -> diff A B ~ diff C D.                       *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 1]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 2; Var 0]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "diff") (args [Var 3; Var 2])
            ; IdentT (Name.local "diff") (args [Var 1; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, A ~ C -> diff A B ~ diff C B.                                  *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "diff") (args [Var 2; Var 1])
          ; IdentT (Name.local "diff") (args [Var 0; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, B ~ C -> diff A B ~ diff A C.                                  *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "diff") (args [Var 2; Var 1])
          ; IdentT (Name.local "diff") (args [Var 2; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C D, A <= C -> D <= B -> diff A B <= diff C D.                    *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 3; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 2]))
        (IdentT (Name.local "Incl")
          (args
            [ IdentT (Name.local "diff") (args [Var 3; Var 2])
            ; IdentT (Name.local "diff") (args [Var 1; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, A <= C -> diff A B <= diff C B.                                *)
Definition InclCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 0]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "diff") (args [Var 2; Var 1])
          ; IdentT (Name.local "diff") (args [Var 0; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, C <= B -> diff A B <= diff A C.                                *)
Definition InclCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "diff") (args [Var 2; Var 1])
          ; IdentT (Name.local "diff") (args [Var 2; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, Small A -> Small (diff A B).                                     *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 1]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "diff") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, diff A B ~ empty <-> A <= B.                                     *)
Definition WhenZero : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "diff") (args [Var 1; Var 0])
          ; IdentT (Name.local "empty") (args [])
          ]))
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, not diff A B ~ empty -> not A ~ B.                               *)
Definition WhenNotZero : DeclP :=
  let concl :=
    Imp
      (Not
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "diff") (args [Var 1; Var 0])
            ; IdentT (Name.local "empty") (args [])
            ])))
      (Not (IdentT (Name.local "equiv") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, B <= A -> (not diff A B ~ empty <-> not A ~ B).                  *)
Definition WhenIncl : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
      (Iff
        (Not
          (IdentT (Name.local "equiv")
            (args
              [ IdentT (Name.local "diff") (args [Var 1; Var 0])
              ; IdentT (Name.local "empty") (args [])
              ])))
        (Not (IdentT (Name.local "equiv") (args [Var 1; Var 0]))))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, B < A -> not diff A B ~ empty.                                   *)
Definition WhenLess : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Less") (args [Var 0; Var 1]))
      (Not
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "diff") (args [Var 1; Var 0])
            ; IdentT (Name.local "empty") (args [])
            ])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, diff A (union2 B C) ~ inter2 (diff A B) (diff A C).            *)
Definition UnionR : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "diff")
            (args
              [ Var 2
              ; IdentT (Name.local "union2") (args [Var 1; Var 0])
              ])
        ; IdentT (Name.local "inter2")
            (args
              [ IdentT (Name.local "diff") (args [Var 2; Var 1])
              ; IdentT (Name.local "diff") (args [Var 2; Var 0])
              ])
        ])
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, Functional (converse F) -> F:[diff A B] ~ diff F[A] F[B].      *)
Definition Image : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional")
        (args [IdentT (Name.local "converse") (args [Var 2])]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args
                [ Var 2
                ; IdentT (Name.local "diff") (args [Var 1; Var 0])
                ])
          ; IdentT (Name.local "diff")
              (args
                [ IdentT (Name.local "image") (args [Var 2; Var 1])
                ; IdentT (Name.local "image") (args [Var 2; Var 0])
                ])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, Proper A -> Proper (diff A (toClass a)).                         *)
Definition IsProper : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Proper") (args [Var 1]))
      (IdentT (Name.local "Proper")
        (args
          [ IdentT (Name.local "diff")
              (args
                [ Var 1
                ; IdentT (Name.local "toClass") (args [Var 0])
                ])
          ]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, diff A B <= A.                                                   *)
Definition IsInclL : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [IdentT (Name.local "diff") (args [Var 1; Var 0]); Var 1])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, diff A B <= complement B.                                        *)
Definition IsInclR : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args
        [ IdentT (Name.local "diff") (args [Var 1; Var 0])
        ; IdentT (Name.local "complement") (args [Var 0])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Classic.exports
  ; Env.unqualify Complement.exports
  ; Env.unqualify Class.Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify IsSetOf.exports
  ; Env.unqualify Less.exports
  ; Env.unqualify Proper.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify Class.Union2.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "diff", diff)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat" , EquivCompat)
      ; (Name.local "EquivCompatL", EquivCompatL)
      ; (Name.local "EquivCompatR", EquivCompatR)
      ; (Name.local "InclCompat"  , InclCompat)
      ; (Name.local "InclCompatL" , InclCompatL)
      ; (Name.local "InclCompatR" , InclCompatR)
      ; (Name.local "IsSmall"     , IsSmall)
      ; (Name.local "WhenZero"    , WhenZero)
      ; (Name.local "WhenNotZero" , WhenNotZero)
      ; (Name.local "WhenIncl"    , WhenIncl)
      ; (Name.local "WhenLess"    , WhenLess)
      ; (Name.local "UnionR"      , UnionR)
      ; (Name.local "Image"       , Image)
      ; (Name.local "IsProper"    , IsProper)
      ; (Name.local "IsInclL"     , IsInclL)
      ; (Name.local "IsInclR"     , IsInclR)
      ]
  ].

Definition env : Env := Env.union imports exports.
