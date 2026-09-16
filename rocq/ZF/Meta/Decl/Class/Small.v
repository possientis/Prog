Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Replacement.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* Small P <-> exists a, forall x, x :< a <-> P x.                              *)
Definition Small : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      Ex
        (All
          (Iff
            (Elem (Var 0) (Var 1))
            (App (Var 2) (Var 0))))
  |}.

(* forall a, Small (toClass a).                                                 *)
Definition SetIsSmall : DeclP :=
  let concl :=
    IdentT (Name.local "Small")
      (args [IdentT (Name.local "toClass") (args [Var 0])])
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P, Small P <-> exists a, equiv P (toClass a).                         *)
Definition IsSomeSet : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Small") (args [Var 0]))
      (Ex
        (IdentT (Name.local "equiv")
          (args [Var 1; IdentT (Name.local "toClass") (args [Var 0])])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, equiv P Q -> Small P -> Small Q.                                 *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 1]))
        (IdentT (Name.local "Small") (args [Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, Incl A B -> Small B -> Small A.                                  *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small") (args [Var 1])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Replacement.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Small", Small)
      ]
  ; Env.fromListP
      [ (Name.local "SetIsSmall" , SetIsSmall)
      ; (Name.local "IsSomeSet"  , IsSomeSet)
      ; (Name.local "EquivCompat", EquivCompat)
      ; (Name.local "InclCompat" , InclCompat)
      ]
  ].

Definition env : Env := Env.union imports exports.
