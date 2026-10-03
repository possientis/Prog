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
Require Import ZF.Meta.Decl.Class.Inter.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* interGen A B := inter (fun y => exists x, A x and y = B!x).                  *)
Definition interGen : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      IdentT (Name.local "inter")
        (args
          [ Lam
              (Ex
                (And
                  (App (Var 3) (Var 0))
                  (SyntaxT.Equal
                    (Var 1)
                    (IdentT (Name.local "eval") (args [Var 2; Var 0])))))
          ])
  |}.

(* forall A B x y, interGen A B y -> A x -> y :< B!x.                           *)
Definition Charac : DeclP :=
  let concl :=
    Imp
      (App (IdentT (Name.local "interGen") (args [Var 3; Var 2])) (Var 0))
      (Imp
        (App (Var 3) (Var 1))
        (Elem
          (Var 0)
          (IdentT (Name.local "eval") (args [Var 2; Var 1]))))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B y, pointwise membership implies membership in interGen A B.       *)
Definition CharacRev : DeclP :=
  let concl :=
    Imp
      (Not
        (IdentT (Name.local "equiv")
          (args [Var 2; IdentT (Name.local "empty") (args [])])))
      (Imp
        (All
          (Imp
            (App (Var 3) (Var 0))
            (Elem
              (Var 1)
              (IdentT (Name.local "eval") (args [Var 2; Var 0])))))
        (App (IdentT (Name.local "interGen") (args [Var 2; Var 1])) (Var 0)))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, Small (interGen A B).                                            *)
Definition IsSmall : DeclP :=
  let concl :=
    IdentT (Name.local "Small")
      (args [IdentT (Name.local "interGen") (args [Var 1; Var 0])])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, equiv A empty -> equiv (interGen A B) empty.                     *)
Definition WhenZero : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv")
        (args [Var 1; IdentT (Name.local "empty") (args [])]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "interGen") (args [Var 1; Var 0])
          ; IdentT (Name.local "empty") (args [])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Class.Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Inter.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify EvalOfClass.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "interGen", interGen)
      ]
  ; Env.fromListP
      [ (Name.local "Charac"    , Charac)
      ; (Name.local "CharacRev" , CharacRev)
      ; (Name.local "IsSmall"   , IsSmall)
      ; (Name.local "WhenZero"  , WhenZero)
      ]
  ].

Definition env : Env := Env.union imports exports.
