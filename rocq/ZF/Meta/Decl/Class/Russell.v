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
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.Specify.

(* Ru x <-> not x :< x.                                                         *)
Definition Ru : DeclT :=
  {| paraT := []
  ;  resT  := TyClass
  ;  bodyT := Lam (Not (Elem (Var 0) (Var 0)))
  |}.

(* Proper Ru.                                                                   *)
Definition ProperRu : DeclP :=
  let concl :=
    IdentT (Name.local "Proper")
      (args [IdentT (Name.local "Ru") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* not exists a, forall x, x :< a.                                              *)
Definition Russell : DeclP :=
  let concl :=
    Not
      (Ex
        (All
          (Elem (Var 0) (Var 1))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Proper.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify Specify.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Ru", Ru)
      ]
  ; Env.fromListP
      [ (Name.local "ProperRu", ProperRu)
      ; (Name.local "Russell" , Russell)
      ]
  ].

Definition env : Env := Env.union imports exports.
