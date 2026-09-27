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
Require Import ZF.Meta.Decl.Class.Proper.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Class.V.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Single.

(* Singleton x <-> exists y, x = single y.                                      *)
Definition Singleton : DeclT :=
  {| paraT := []
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (SyntaxT.Equal
            (Var 1)
            (IdentT (Name.local "single") (args [Var 0]))))
  |}.

(* Proper Singleton.                                                            *)
Definition IsProper : DeclP :=
  let concl :=
    IdentT (Name.local "Proper")
      (args [IdentT (Name.local "Singleton") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Proper.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify V.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify Single.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Singleton", Singleton)
      ]
  ; Env.fromListP
      [ (Name.local "IsProper", IsProper)
      ]
  ].

Definition env : Env := Env.union imports exports.
