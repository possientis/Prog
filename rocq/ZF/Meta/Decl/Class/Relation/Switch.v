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
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* Switch is the class of ordered pairs of the form ((y,z),(z,y)).              *)
Definition Switch : DeclT :=
  {| paraT := []
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (Ex
            (SyntaxT.Equal
              (Var 2)
              (IdentT (Name.local "ordPair")
                (args
                  [ IdentT (Name.local "ordPair") (args [Var 1; Var 0])
                  ; IdentT (Name.local "ordPair") (args [Var 0; Var 1])
                  ])))))
  |}.

(* forall x x', Switch (x,x') iff exists y z, x = (y,z) and x' = (z,y).         *)
Definition Charac2 : DeclP :=
  let concl :=
    Iff
      (App (IdentT (Name.local "Switch") (args []))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (Ex
        (Ex
          (And
            (SyntaxT.Equal
              (Var 3)
              (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
            (SyntaxT.Equal
              (Var 2)
              (IdentT (Name.local "ordPair") (args [Var 0; Var 1]))))))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Switch is functional.                                                        *)
Definition IsFunctional : DeclP :=
  let concl :=
    IdentT (Name.local "Functional")
      (args [IdentT (Name.local "Switch") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Switch", Switch)
      ]
  ; Env.fromListP
      [ (Name.local "Charac2"     , Charac2)
      ; (Name.local "IsFunctional", IsFunctional)
      ]
  ].

Definition env : Env := Env.union imports exports.
