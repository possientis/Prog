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

Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Order.Restrict.
Require Import ZF.Meta.Decl.Class.Order.Transport.
Require Import ZF.Meta.Decl.Class.Prod.
Require Import ZF.Meta.Decl.Class.Relation.Bij.
Require Import ZF.Meta.Decl.Class.Relation.Compose.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* Isom F R S A B says F is an (R,S)-isomorphism from A to B.                   *)
Definition Isom : DeclT :=
  {| paraT := [TyClass; TyClass; TyClass; TyClass; TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      And
        (IdentT (Name.local "Bij") (args [Var 4; Var 1; Var 0]))
        (All
          (All
            (Imp
              (App (Var 3) (Var 1))
              (Imp
                (App (Var 3) (Var 0))
                (Iff
                  (App (Var 5)
                    (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
                  (App (Var 4)
                    (IdentT (Name.local "ordPair")
                      (args
                        [ IdentT (Name.local "eval") (args [Var 6; Var 1])
                        ; IdentT (Name.local "eval") (args [Var 6; Var 0])
                        ]))))))))
  |}.

(* forall F R S A B F' R' S' A' B', Isom respects equivalence.                  *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 9; Var 4]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 8; Var 3]))
        (Imp
          (IdentT (Name.local "equiv") (args [Var 7; Var 2]))
          (Imp
            (IdentT (Name.local "equiv") (args [Var 6; Var 1]))
            (Imp
              (IdentT (Name.local "equiv") (args [Var 5; Var 0]))
              (Imp
                (IdentT (Name.local "Isom")
                  (args [Var 9; Var 8; Var 7; Var 6; Var 5]))
                (IdentT (Name.local "Isom")
                  (args [Var 4; Var 3; Var 2; Var 1; Var 0])))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass;
                  TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G R S A B, equivalent functions preserve isomorphism.               *)
Definition EquivCompat1 : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 5; Var 4]))
      (Imp
        (IdentT (Name.local "Isom") (args [Var 5; Var 3; Var 2; Var 1; Var 0]))
        (IdentT (Name.local "Isom") (args [Var 4; Var 3; Var 2; Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F R R' S A B, equivalent source relations preserve isomorphism.       *)
Definition EquivCompat2 : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 4; Var 3]))
      (Imp
        (IdentT (Name.local "Isom") (args [Var 5; Var 4; Var 2; Var 1; Var 0]))
        (IdentT (Name.local "Isom") (args [Var 5; Var 3; Var 2; Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F R S S' A B, equivalent target relations preserve isomorphism.       *)
Definition EquivCompat3 : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "Isom") (args [Var 5; Var 4; Var 3; Var 1; Var 0]))
        (IdentT (Name.local "Isom") (args [Var 5; Var 4; Var 2; Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F R S A A' B, equivalent domains preserve isomorphism.                *)
Definition EquivCompat4 : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Isom") (args [Var 5; Var 4; Var 3; Var 2; Var 0]))
        (IdentT (Name.local "Isom") (args [Var 5; Var 4; Var 3; Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F R S A B B', equivalent codomains preserve isomorphism.              *)
Definition EquivCompat5 : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Isom") (args [Var 5; Var 4; Var 3; Var 2; Var 1]))
        (IdentT (Name.local "Isom") (args [Var 5; Var 4; Var 3; Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F R S A B, restricting the source relation to A preserves Isom.       *)
Definition RestrictL : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Isom") (args [Var 4; Var 3; Var 2; Var 1; Var 0]))
      (IdentT (Name.local "Isom")
        (args
          [ Var 4
          ; IdentT (Name.local "restrict") (args [Var 3; Var 1])
          ; Var 2
          ; Var 1
          ; Var 0
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F R S A B, restricting the target relation to B preserves Isom.       *)
Definition RestrictR : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Isom") (args [Var 4; Var 3; Var 2; Var 1; Var 0]))
      (IdentT (Name.local "Isom")
        (args
          [ Var 4
          ; Var 3
          ; IdentT (Name.local "restrict") (args [Var 2; Var 0])
          ; Var 1
          ; Var 0
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F R S A B, the converse of an isomorphism is an isomorphism.          *)
Definition Converse : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Isom") (args [Var 4; Var 3; Var 2; Var 1; Var 0]))
      (IdentT (Name.local "Isom")
        (args
          [ IdentT (Name.local "converse") (args [Var 4])
          ; Var 2
          ; Var 3
          ; Var 0
          ; Var 1
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G R S T A B C, the composition of isomorphisms is an isomorphism.   *)
Definition Compose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Isom") (args [Var 7; Var 5; Var 4; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Isom") (args [Var 6; Var 4; Var 3; Var 1; Var 0]))
        (IdentT (Name.local "Isom")
          (args
            [ IdentT (Name.local "compose") (args [Var 6; Var 7])
            ; Var 5
            ; Var 3
            ; Var 2
            ; Var 0
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F R S A B, any equivalent transport along a bijection is an isom.     *)
Definition Transport : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv")
        (args
          [ Var 2
          ; IdentT (Name.local "transport") (args [Var 4; Var 3; Var 1])
          ]))
      (Imp
        (IdentT (Name.local "Bij") (args [Var 4; Var 1; Var 0]))
        (IdentT (Name.local "Isom") (args [Var 4; Var 3; Var 2; Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Class.Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Order.Restrict.exports
  ; Env.unqualify Transport.exports
  ; Env.unqualify Prod.exports
  ; Env.unqualify Bij.exports
  ; Env.unqualify Compose.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify EvalOfClass.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Isom", Isom)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat" , EquivCompat)
      ; (Name.local "EquivCompat1", EquivCompat1)
      ; (Name.local "EquivCompat2", EquivCompat2)
      ; (Name.local "EquivCompat3", EquivCompat3)
      ; (Name.local "EquivCompat4", EquivCompat4)
      ; (Name.local "EquivCompat5", EquivCompat5)
      ; (Name.local "RestrictL"   , RestrictL)
      ; (Name.local "RestrictR"   , RestrictR)
      ; (Name.local "Converse"    , Converse)
      ; (Name.local "Compose"     , Compose)
      ; (Name.local "Transport"   , Transport)
      ]
  ].

Definition env : Env := Env.union imports exports.
