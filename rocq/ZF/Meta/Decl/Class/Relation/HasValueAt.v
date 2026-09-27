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
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.FunctionalAt.
Require Import ZF.Meta.Decl.Class.Relation.IsValueAt.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* HasValueAt F a <-> exists y, IsValueAt F a y.                                *)
Definition HasValueAt : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (IdentT (Name.local "IsValueAt") (args [Var 2; Var 1; Var 0])))
  |}.

(* forall F, HasValueAt F ~ (fun a => FunctionalAt F a) /\ domain F.            *)
Definition AsInter : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "HasValueAt") (args [Var 0])
        ; IdentT (Name.local "inter2")
            (args
              [ Lam (IdentT (Name.local "FunctionalAt") (args [Var 1; Var 0]))
              ; IdentT (Name.local "domain") (args [Var 0])
              ])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, FunctionalAt F a -> HasValueAt F a <-> domain F a.               *)
Definition WhenFunctionalAt : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "FunctionalAt") (args [Var 1; Var 0]))
      (Iff
        (App (IdentT (Name.local "HasValueAt") (args [Var 1])) (Var 0))
        (App (IdentT (Name.local "domain") (args [Var 1])) (Var 0)))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Functional F -> HasValueAt F ~ domain F.                           *)
Definition WhenFunctional : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "HasValueAt") (args [Var 0])
          ; IdentT (Name.local "domain") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify FunctionalAt.exports
  ; Env.unqualify IsValueAt.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "HasValueAt", HasValueAt)
      ]
  ; Env.fromListP
      [ (Name.local "AsInter"          , AsInter)
      ; (Name.local "WhenFunctionalAt", WhenFunctionalAt)
      ; (Name.local "WhenFunctional"  , WhenFunctional)
      ]
  ].

Definition env : Env := Env.union imports exports.
