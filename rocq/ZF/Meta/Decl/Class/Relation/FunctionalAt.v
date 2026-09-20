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
Require Import ZF.Meta.Decl.Set.OrdPair.

(* FunctionalAt F a <-> forall y z, F :(a,y): -> F :(a,z): -> y = z.            *)
Definition FunctionalAt : DeclT :=
  {| paraT := [TyClass; TySet]
  ;  resT  := TyProp
  ;  bodyT :=
      All
        (All
          (Imp
            (App (Var 3)
              (IdentT (Name.local "ordPair") (args [Var 2; Var 1])))
            (Imp
              (App (Var 3)
                (IdentT (Name.local "ordPair") (args [Var 2; Var 0])))
              (SyntaxT.Equal (Var 1) (Var 0)))))
  |}.

(* forall F G a, equiv F G -> FunctionalAt F a -> FunctionalAt G a.             *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "FunctionalAt") (args [Var 2; Var 0]))
        (IdentT (Name.local "FunctionalAt") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, ~ FunctionalAt F a <->                                           *)
(*   exists y z, y <> z /\ F :(a,y): /\ F :(a,z):.                              *)
Definition WhenNot : DeclP :=
  let concl :=
    Iff
      (Not (IdentT (Name.local "FunctionalAt") (args [Var 1; Var 0])))
      (Ex
        (Ex
          (And
            (NotEq (Var 1) (Var 0))
            (And
              (App (Var 3)
                (IdentT (Name.local "ordPair") (args [Var 2; Var 1])))
              (App (Var 3)
                (IdentT (Name.local "ordPair") (args [Var 2; Var 0])))))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "FunctionalAt", FunctionalAt)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat", EquivCompat)
      ; (Name.local "WhenNot"    , WhenNot)
      ]
  ].

Definition env : Env := Env.union imports exports.
