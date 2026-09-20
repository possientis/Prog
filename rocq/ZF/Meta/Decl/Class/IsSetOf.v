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

Require Import ZF.Meta.Decl.Axiom.Define.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Small.

(* IsSetOf A a <-> forall x, x :< a <-> A x.                                    *)
Definition IsSetOf : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (All
          (Iff
            (Elem (Var 0) (Var 1))
            (App (Var 2) (Var 0))))
  |}.

(* forall A, Small A -> Exists (IsSetOf A).                                     *)
Definition Exists : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 0]))
      (IdentT (Name.local "Exists")
        (args [IdentT (Name.local "IsSetOf") (args [Var 0])]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, Unique (IsSetOf A).                                                *)
Definition Unique : DeclP :=
  let concl :=
    IdentT (Name.local "Unique")
      (args [IdentT (Name.local "IsSetOf") (args [Var 0])])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, equiv A B -> equiv (IsSetOf A) (IsSetOf B).                      *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args [IdentT (Name.local "IsSetOf") (args [Var 1]);
         IdentT (Name.local "IsSetOf") (args [Var 0])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, IsSetOf A a <-> equiv (toClass a) A.                             *)
Definition ToClass : DeclP :=
  let concl :=
    Iff
      (App (IdentT (Name.local "IsSetOf") (args [Var 1])) (Var 0))
      (IdentT (Name.local "equiv")
        (args [IdentT (Name.local "toClass") (args [Var 0]); Var 1]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Define.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Small.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "IsSetOf", IsSetOf)
      ]
  ; Env.fromListP
      [ (Name.local "Exists"     , Exists)
      ; (Name.local "Unique"     , Unique)
      ; (Name.local "EquivCompat", EquivCompat)
      ; (Name.local "ToClass"    , ToClass)
      ]
  ].

Definition env : Env := Env.union imports exports.
