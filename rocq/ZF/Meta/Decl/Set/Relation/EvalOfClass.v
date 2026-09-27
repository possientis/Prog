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

Require Import ZF.Meta.Decl.Axiom.Classic.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Eval.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.FunctionalAt.
Require Import ZF.Meta.Decl.Class.Relation.HasValueAt.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* eval F a := fromClass (class-eval F a).                                      *)
Definition eval : DeclT :=
  {| paraT := [TyClass; TySet]
  ;  resT  := TySet
  ;  bodyT := FromC (IdentT (Name.qualified "CRE" "eval") (args [Var 1; Var 0]))
  |}.

(* forall F G a, F ~ G -> eval F a = eval G a.                                  *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (SyntaxT.Equal
        (IdentT (Name.local "eval") (args [Var 2; Var 0]))
        (IdentT (Name.local "eval") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, HasValueAt F a -> F :(a,y): <-> eval F a = y.                  *)
Definition HasValueAtEvalCharac : DeclP :=
  let concl :=
    Imp
      (App (IdentT (Name.local "HasValueAt") (args [Var 2])) (Var 1))
      (Iff
        (App (Var 2) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
        (SyntaxT.Equal
          (IdentT (Name.local "eval") (args [Var 2; Var 1]))
          (Var 0)))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, HasValueAt F a -> F :(a, eval F a):.                             *)
Definition HasValueAtSatisfies : DeclP :=
  let concl :=
    Imp
      (App (IdentT (Name.local "HasValueAt") (args [Var 1])) (Var 0))
      (App
        (Var 1)
        (IdentT (Name.local "ordPair")
          (args [Var 0; IdentT (Name.local "eval") (args [Var 1; Var 0])])))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, FunctionalAt F a -> domain F a -> F :(a,y): <-> eval F a = y.  *)
Definition FunctionalAtEvalCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "FunctionalAt") (args [Var 2; Var 1]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 2])) (Var 1))
        (Iff
          (App (Var 2) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
          (SyntaxT.Equal
            (IdentT (Name.local "eval") (args [Var 2; Var 1]))
            (Var 0))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, FunctionalAt F a -> domain F a -> F :(a, eval F a):.             *)
Definition FunctionalAtSatisfies : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "FunctionalAt") (args [Var 1; Var 0]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 1])) (Var 0))
        (App
          (Var 1)
          (IdentT (Name.local "ordPair")
            (args [Var 0; IdentT (Name.local "eval") (args [Var 1; Var 0])]))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, not HasValueAt F a -> eval F a = empty.                          *)
Definition WhenNotHasValueAt : DeclP :=
  let concl :=
    Imp
      (Not (App (IdentT (Name.local "HasValueAt") (args [Var 1])) (Var 0)))
      (SyntaxT.Equal
        (IdentT (Name.local "eval") (args [Var 1; Var 0]))
        (IdentT (Name.local "empty") (args [])))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, not FunctionalAt F a -> eval F a = empty.                        *)
Definition WhenNotFunctionalAt : DeclP :=
  let concl :=
    Imp
      (Not (IdentT (Name.local "FunctionalAt") (args [Var 1; Var 0])))
      (SyntaxT.Equal
        (IdentT (Name.local "eval") (args [Var 1; Var 0]))
        (IdentT (Name.local "empty") (args [])))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, not domain F a -> eval F a = empty.                              *)
Definition WhenNotInDomain : DeclP :=
  let concl :=
    Imp
      (Not (App (IdentT (Name.local "domain") (args [Var 1])) (Var 0)))
      (SyntaxT.Equal
        (IdentT (Name.local "eval") (args [Var 1; Var 0]))
        (IdentT (Name.local "empty") (args [])))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, Functional F -> domain F a -> F :(a,y): <-> eval F a = y.      *)
Definition Charac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 2])) (Var 1))
        (Iff
          (App (Var 2) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
          (SyntaxT.Equal
            (IdentT (Name.local "eval") (args [Var 2; Var 1]))
            (Var 0))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, Functional F -> domain F a -> F :(a, eval F a):.                 *)
Definition Satisfies : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 1])) (Var 0))
        (App
          (Var 1)
          (IdentT (Name.local "ordPair")
            (args [Var 0; IdentT (Name.local "eval") (args [Var 1; Var 0])]))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, Functional F -> domain F a -> range F (eval F a).                *)
Definition IsInRange : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 1])) (Var 0))
        (App
          (IdentT (Name.local "range") (args [Var 1]))
          (IdentT (Name.local "eval") (args [Var 1; Var 0]))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, Functional F -> image F A y iff exists x, A x and F!x = y.       *)
Definition ImageCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (All
        (Iff
          (App (IdentT (Name.local "image") (args [Var 2; Var 1])) (Var 0))
          (Ex
            (And
              (App (Var 2) (Var 0))
              (And
                (App (IdentT (Name.local "domain") (args [Var 3])) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 3; Var 0]))
                  (Var 1)))))))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Classic.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Domain.exports
  ; Env.qualifyAs "CRE" Eval.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify FunctionalAt.exports
  ; Env.unqualify HasValueAt.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify Empty.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "eval", eval)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat"          , EquivCompat)
      ; (Name.local "HasValueAtEvalCharac" , HasValueAtEvalCharac)
      ; (Name.local "HasValueAtSatisfies"  , HasValueAtSatisfies)
      ; (Name.local "FunctionalAtEvalCharac", FunctionalAtEvalCharac)
      ; (Name.local "FunctionalAtSatisfies" , FunctionalAtSatisfies)
      ; (Name.local "WhenNotHasValueAt"    , WhenNotHasValueAt)
      ; (Name.local "WhenNotFunctionalAt"  , WhenNotFunctionalAt)
      ; (Name.local "WhenNotInDomain"      , WhenNotInDomain)
      ; (Name.local "Charac"               , Charac)
      ; (Name.local "Satisfies"            , Satisfies)
      ; (Name.local "IsInRange"            , IsInRange)
      ; (Name.local "ImageCharac"          , ImageCharac)
      ]
  ].

Definition env : Env := Env.union imports exports.
