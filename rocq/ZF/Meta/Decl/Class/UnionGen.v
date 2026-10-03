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
Require Import ZF.Meta.Decl.Class.Union.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* unionGen A B y <-> exists x, A x /\ y :< B!x.                                *)
Definition unionGen : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (And
            (App (Var 3) (Var 0))
            (Elem
              (Var 1)
              (IdentT (Name.local "eval") (args [Var 2; Var 0])))))
  |}.

(* forall A B y, unionGen A B y iff exists x, A x and y :< B!x.                 *)
Definition Charac : DeclP :=
  let concl :=
    All
      (Iff
        (App (IdentT (Name.local "unionGen") (args [Var 2; Var 1])) (Var 0))
        (Ex
          (And
            (App (Var 3) (Var 0))
            (Elem
              (Var 1)
              (IdentT (Name.local "eval") (args [Var 2; Var 0]))))))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, pointwise equality on A makes the unions equivalent.           *)
Definition Equal : DeclP :=
  let concl :=
    Imp
      (All
        (Imp
          (App (Var 3) (Var 0))
          (SyntaxT.Equal
            (IdentT (Name.local "eval") (args [Var 2; Var 0]))
            (IdentT (Name.local "eval") (args [Var 1; Var 0])))))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "unionGen") (args [Var 2; Var 1])
          ; IdentT (Name.local "unionGen") (args [Var 2; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B x, A x -> toClass (B!x) is included in unionGen A B.              *)
Definition IsIncl : DeclP :=
  let concl :=
    Imp
      (App (Var 2) (Var 0))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "toClass")
              (args [IdentT (Name.local "eval") (args [Var 1; Var 0])])
          ; IdentT (Name.local "unionGen") (args [Var 2; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, Small A -> Small (unionGen A B).                                 *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 1]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "unionGen") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C D, inclusion of indices and values gives inclusion.             *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 3; Var 1]))
      (Imp
        (All
          (Imp
            (App (Var 4) (Var 0))
            (IdentT (Name.local "Incl")
              (args
                [ IdentT (Name.local "toClass")
                    (args [IdentT (Name.local "eval") (args [Var 3; Var 0])])
                ; IdentT (Name.local "toClass")
                    (args [IdentT (Name.local "eval") (args [Var 1; Var 0])])
                ]))))
        (IdentT (Name.local "Incl")
          (args
            [ IdentT (Name.local "unionGen") (args [Var 3; Var 2])
            ; IdentT (Name.local "unionGen") (args [Var 1; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, Incl A C -> Incl (unionGen A B) (unionGen C B).                *)
Definition InclCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 0]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "unionGen") (args [Var 2; Var 1])
          ; IdentT (Name.local "unionGen") (args [Var 0; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, pointwise value inclusion gives union inclusion.               *)
Definition InclCompatR : DeclP :=
  let concl :=
    Imp
      (All
        (Imp
          (App (Var 3) (Var 0))
          (IdentT (Name.local "Incl")
            (args
              [ IdentT (Name.local "toClass")
                  (args [IdentT (Name.local "eval") (args [Var 2; Var 0])])
              ; IdentT (Name.local "toClass")
                  (args [IdentT (Name.local "eval") (args [Var 1; Var 0])])
              ]))))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "unionGen") (args [Var 2; Var 1])
          ; IdentT (Name.local "unionGen") (args [Var 2; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, pointwise bounded values bound the generalized union.          *)
Definition WhenBounded : DeclP :=
  let concl :=
    Imp
      (All
        (Imp
          (App (Var 3) (Var 0))
          (IdentT (Name.local "Incl")
            (args
              [ IdentT (Name.local "toClass")
                  (args [IdentT (Name.local "eval") (args [Var 2; Var 0])])
              ; Var 1
              ]))))
      (IdentT (Name.local "Incl")
        (args [IdentT (Name.local "unionGen") (args [Var 2; Var 1]); Var 0]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify Union.exports
  ; Env.unqualify EvalOfClass.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "unionGen", unionGen)
      ]
  ; Env.fromListP
      [ (Name.local "Charac"       , Charac)
      ; (Name.local "Equal"        , Equal)
      ; (Name.local "IsIncl"       , IsIncl)
      ; (Name.local "IsSmall"      , IsSmall)
      ; (Name.local "InclCompat"   , InclCompat)
      ; (Name.local "InclCompatL"  , InclCompatL)
      ; (Name.local "InclCompatR"  , InclCompatR)
      ; (Name.local "WhenBounded"  , WhenBounded)
      ]
  ].

Definition env : Env := Env.union imports exports.
