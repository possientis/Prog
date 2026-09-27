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
Require Import ZF.Meta.Decl.Class.Union.
Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Incl.
Require Import ZF.Meta.Decl.Set.Single.

(* union a : U.                                                                 *)
Definition union : DeclT :=
  {| paraT := [TySet]
  ;  resT  := TySet
  ;  bodyT :=
      FromC
        (IdentT (Name.qualified "CUN" "union")
          (args [IdentT (Name.local "toClass") (args [Var 0])]))
  |}.

(* forall a x, x :< union a <-> exists y, x :< y /\ y :< a.                     *)
Definition Charac : DeclP :=
  let concl :=
    All
      (Iff
        (Elem (Var 0) (IdentT (Name.local "union") (args [Var 1])))
        (Ex
          (And
            (Elem (Var 1) (Var 0))
            (Elem (Var 0) (Var 2)))))
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, equiv (toClass (union a)) (CUN.union (toClass a)).                 *)
Definition ToClass : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "toClass")
            (args [IdentT (Name.local "union") (args [Var 0])])
        ; IdentT (Name.qualified "CUN" "union")
            (args [IdentT (Name.local "toClass") (args [Var 0])])
        ])
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* union empty = empty.                                                         *)
Definition WhenZero : DeclP :=
  let concl :=
    SyntaxT.Equal
      (IdentT (Name.local "union")
        (args [IdentT (Name.local "empty") (args [])]))
      (IdentT (Name.local "empty") (args []))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, union (single a) = a.                                              *)
Definition WhenSingleton : DeclP :=
  let concl :=
    SyntaxT.Equal
      (IdentT (Name.local "union")
        (args [IdentT (Name.local "single") (args [Var 0])]))
      (Var 0)
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.qualifyAs "CUN" Union.exports
  ; Env.unqualify Empty.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify Single.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "union", union)
      ]
  ; Env.fromListP
      [ (Name.local "Charac"       , Charac)
      ; (Name.local "ToClass"      , ToClass)
      ; (Name.local "WhenZero"     , WhenZero)
      ; (Name.local "WhenSingleton", WhenSingleton)
      ]
  ].

Definition env : Env := Env.union imports exports.
