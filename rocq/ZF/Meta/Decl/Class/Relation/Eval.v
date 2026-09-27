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
Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.FunctionalAt.
Require Import ZF.Meta.Decl.Class.Relation.HasValueAt.
Require Import ZF.Meta.Decl.Class.Relation.IsValueAt.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* eval F a x <-> exists y, x :< y /\ IsValueAt F a y.                          *)
Definition eval : DeclT :=
  {| paraT := [TyClass; TySet]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (And
            (Elem (Var 1) (Var 0))
            (IdentT (Name.local "IsValueAt") (args [Var 3; Var 2; Var 0]))))
  |}.

(* forall F G a, F ~ G -> eval F a ~ eval G a.                                  *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "eval") (args [Var 2; Var 0])
          ; IdentT (Name.local "eval") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, HasValueAt F a -> F :(a,y): <-> eval F a ~ toClass y.          *)
Definition WhenHasValueAt : DeclP :=
  let concl :=
    Imp
      (App (IdentT (Name.local "HasValueAt") (args [Var 2])) (Var 1))
      (Iff
        (App (Var 2) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "eval") (args [Var 2; Var 1])
            ; IdentT (Name.local "toClass") (args [Var 0])
            ])))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, FunctionalAt F a -> domain F a -> iff as above.                *)
Definition WhenFunctionalAt : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "FunctionalAt") (args [Var 2; Var 1]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 2])) (Var 1))
        (Iff
          (App (Var 2) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
          (IdentT (Name.local "equiv")
            (args
              [ IdentT (Name.local "eval") (args [Var 2; Var 1])
              ; IdentT (Name.local "toClass") (args [Var 0])
              ]))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, Functional F -> domain F a -> iff as above.                    *)
Definition WhenFunctional : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 2])) (Var 1))
        (Iff
          (App (Var 2) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
          (IdentT (Name.local "equiv")
            (args
              [ IdentT (Name.local "eval") (args [Var 2; Var 1])
              ; IdentT (Name.local "toClass") (args [Var 0])
              ]))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, not HasValueAt F a -> eval F a ~ empty.                          *)
Definition WhenNotHasValueAt : DeclP :=
  let concl :=
    Imp
      (Not (App (IdentT (Name.local "HasValueAt") (args [Var 1])) (Var 0)))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "eval") (args [Var 1; Var 0])
          ; IdentT (Name.local "empty") (args [])
          ]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, not FunctionalAt F a -> eval F a ~ empty.                        *)
Definition WhenNotFunctionalAt : DeclP :=
  let concl :=
    Imp
      (Not (IdentT (Name.local "FunctionalAt") (args [Var 1; Var 0])))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "eval") (args [Var 1; Var 0])
          ; IdentT (Name.local "empty") (args [])
          ]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, not domain F a -> eval F a ~ empty.                              *)
Definition WhenNotInDomain : DeclP :=
  let concl :=
    Imp
      (Not (App (IdentT (Name.local "domain") (args [Var 1])) (Var 0)))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "eval") (args [Var 1; Var 0])
          ; IdentT (Name.local "empty") (args [])
          ]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, Small (eval F a).                                                *)
Definition IsSmall : DeclP :=
  let concl :=
    IdentT (Name.local "Small")
      (args [IdentT (Name.local "eval") (args [Var 1; Var 0])])
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Classic.exports
  ; Env.unqualify Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify FunctionalAt.exports
  ; Env.unqualify HasValueAt.exports
  ; Env.unqualify IsValueAt.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "eval", eval)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat"        , EquivCompat)
      ; (Name.local "WhenHasValueAt"     , WhenHasValueAt)
      ; (Name.local "WhenFunctionalAt"   , WhenFunctionalAt)
      ; (Name.local "WhenFunctional"     , WhenFunctional)
      ; (Name.local "WhenNotHasValueAt"  , WhenNotHasValueAt)
      ; (Name.local "WhenNotFunctionalAt", WhenNotFunctionalAt)
      ; (Name.local "WhenNotInDomain"    , WhenNotInDomain)
      ; (Name.local "IsSmall"            , IsSmall)
      ]
  ].

Definition env : Env := Env.union imports exports.
