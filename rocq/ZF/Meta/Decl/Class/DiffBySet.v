Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Class.Complement.
Require Import ZF.Meta.Decl.Class.Diff.
Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Less.
Require Import ZF.Meta.Decl.Class.Proper.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Incl.
Require Import ZF.Meta.Decl.Set.Relation.ImageUnderClass.
Require Import ZF.Meta.Decl.Set.Union2.

(* diff A a := class-diff A (toClass a).                                        *)
Definition diff : DeclT :=
  {| paraT := [TyClass; TySet]
  ;  resT  := TyClass
  ;  bodyT :=
      IdentT (Name.qualified "CDI" "diff")
        (args [Var 1; IdentT (Name.local "toClass") (args [Var 0])])
  |}.

(* forall A a x, x is in A minus a iff A x and x is not in a.                   *)
Definition Charac : DeclP :=
  let concl :=
    Iff
      (App (IdentT (Name.local "diff") (args [Var 2; Var 1])) (Var 0))
      (And (App (Var 2) (Var 0)) (Not (Elem (Var 0) (Var 1))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B a, A ~ B -> A minus a is equivalent to B minus a.                 *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "diff") (args [Var 2; Var 0])
          ; IdentT (Name.local "diff") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B a, A <= B -> A minus a is included in B minus a.                  *)
Definition InclCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "diff") (args [Var 2; Var 0])
          ; IdentT (Name.local "diff") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A b c, b <= c -> A minus c is included in A minus b.                  *)
Definition InclCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.qualified "SIN" "Incl") (args [Var 1; Var 0]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "diff") (args [Var 2; Var 0])
          ; IdentT (Name.local "diff") (args [Var 2; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, A minus a is included in A.                                      *)
Definition IsInclL : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [IdentT (Name.local "diff") (args [Var 1; Var 0]); Var 1])
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, A minus a is included in the complement of toClass a.            *)
Definition IsInclR : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args
        [ IdentT (Name.local "diff") (args [Var 1; Var 0])
        ; IdentT (Name.local "complement")
            (args [IdentT (Name.local "toClass") (args [Var 0])])
        ])
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, removing the empty set from A leaves A unchanged.                  *)
Definition IdentityR : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "diff")
            (args [Var 0; IdentT (Name.local "empty") (args [])])
        ; Var 0
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, Small A -> Small (A minus a).                                    *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 1]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "diff") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, Proper A -> Proper (A minus a).                                  *)
Definition IsProper : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Proper") (args [Var 1]))
      (IdentT (Name.local "Proper")
        (args [IdentT (Name.local "diff") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, A minus a is empty iff A is included in toClass a.               *)
Definition WhenZero : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "diff") (args [Var 1; Var 0])
          ; IdentT (Name.qualified "CEM" "empty") (args [])
          ]))
      (IdentT (Name.local "Incl")
        (args [Var 1; IdentT (Name.local "toClass") (args [Var 0])]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, nonempty difference implies A is not equivalent to toClass a.    *)
Definition WhenNotZero : DeclP :=
  let concl :=
    Imp
      (Not
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "diff") (args [Var 1; Var 0])
            ; IdentT (Name.qualified "CEM" "empty") (args [])
            ])))
      (Not
        (IdentT (Name.local "equiv")
          (args [Var 1; IdentT (Name.local "toClass") (args [Var 0])])))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, toClass a <= A relates nonempty difference and inequivalence.    *)
Definition WhenIncl : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl")
        (args [IdentT (Name.local "toClass") (args [Var 0]); Var 1]))
      (Iff
        (Not
          (IdentT (Name.local "equiv")
            (args
              [ IdentT (Name.local "diff") (args [Var 1; Var 0])
              ; IdentT (Name.qualified "CEM" "empty") (args [])
              ])))
        (Not
          (IdentT (Name.local "equiv")
            (args [Var 1; IdentT (Name.local "toClass") (args [Var 0])]))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, toClass a < A -> A minus a is nonempty.                          *)
Definition WhenLess : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Less")
        (args [IdentT (Name.local "toClass") (args [Var 0]); Var 1]))
      (Not
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "diff") (args [Var 1; Var 0])
            ; IdentT (Name.qualified "CEM" "empty") (args [])
            ])))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A b c, A minus union2 b c is (A minus b) inter2 (A minus c).          *)
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
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A a, injective functional image commutes with difference by set.    *)
Definition Image : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional")
        (args [IdentT (Name.local "converse") (args [Var 2])]))
      (Imp
        (IdentT (Name.local "Functional") (args [Var 2]))
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
                  ; IdentT (Name.qualified "SIM" "image") (args [Var 2; Var 0])
                  ])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.
(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Complement.exports
  ; Env.qualifyAs "CDI" Diff.exports
  ; Env.qualifyAs "CEM" Class.Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Less.exports
  ; Env.unqualify Proper.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify Empty.exports
  ; Env.qualifyAs "SIN" Incl.exports
  ; Env.qualifyAs "SIM" ImageUnderClass.exports
  ; Env.unqualify Union2.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "diff", diff)
      ]
  ; Env.fromListP
      [ (Name.local "Charac"       , Charac)
      ; (Name.local "EquivCompat"   , EquivCompat)
      ; (Name.local "InclCompatL"   , InclCompatL)
      ; (Name.local "InclCompatR"   , InclCompatR)
      ; (Name.local "IsInclL"       , IsInclL)
      ; (Name.local "IsInclR"       , IsInclR)
      ; (Name.local "IdentityR"     , IdentityR)
      ; (Name.local "IsSmall"       , IsSmall)
      ; (Name.local "IsProper"      , IsProper)
      ; (Name.local "WhenZero"      , WhenZero)
      ; (Name.local "WhenNotZero"   , WhenNotZero)
      ; (Name.local "WhenIncl"      , WhenIncl)
      ; (Name.local "WhenLess"      , WhenLess)
      ; (Name.local "UnionR"        , UnionR)
      ; (Name.local "Image"         , Image)
      ]
  ].

Definition env : Env := Env.union imports exports.
