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
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Set.Pair.

(* single a : U.                                                                *)
Definition single : DeclT :=
  {| paraT := [TySet]
  ;  resT  := TySet
  ;  bodyT := IdentT (Name.local "pair") (args [Var 0; Var 0])
  |}.

(* forall a x, x :< single a <-> x = a.                                         *)
Definition Charac : DeclP :=
  let concl :=
    All
      (Iff
        (Elem (Var 0) (IdentT (Name.local "single") (args [Var 1])))
        (Equal (Var 0) (Var 1)))
  in
    {| paraP := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, a :< single a.                                                     *)
Definition IsIn : DeclP :=
  let concl :=
    Elem (Var 0) (IdentT (Name.local "single") (args [Var 0]))
  in
    {| paraP := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, single a = single b -> a = b.                                    *)
Definition WhenEqual : DeclP :=
  let concl :=
    Imp
      (Equal
        (IdentT (Name.local "single") (args [Var 1]))
        (IdentT (Name.local "single") (args [Var 0])))
      (Equal (Var 1) (Var 0))
  in
    {| paraP := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, A a <-> Incl (toClass (single a)) A.                             *)
Definition ToClassIncl : DeclP :=
  let concl :=
    Iff
      (App (Var 1) (Var 0))
      (IdentT (Name.local "Incl")
        (args [IdentT (Name.local "toClass")
          (args [IdentT (Name.local "single") (args [Var 0])]);
         Var 1]))
  in
    {| paraP := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b c, b <> c -> single a <> pair b c.                                *)
Definition IsNotPair : DeclP :=
  let concl :=
    Imp
      (NotEq (Var 1) (Var 0))
      (NotEq
        (IdentT (Name.local "single") (args [Var 2]))
        (IdentT (Name.local "pair") (args [Var 1; Var 0])))
  in
    {| paraP := [TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify Pair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "single", single)
      ]
  ; Env.fromListP
      [ (Name.local "Charac"     , Charac)
      ; (Name.local "IsIn"       , IsIn)
      ; (Name.local "WhenEqual"  , WhenEqual)
      ; (Name.local "ToClassIncl", ToClassIncl)
      ; (Name.local "IsNotPair"  , IsNotPair)
      ]
  ].

Definition env : Env := Env.union imports exports.
