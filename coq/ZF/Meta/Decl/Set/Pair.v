Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.

(* Declarations.                                                                *)

(* Definition IsPairOf (a b:U) : Class := fun x =>                              *)
(* forall y, y :< x <-> y = a \/ y = b.                                         *)
Definition IsPairOf : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (All VarTySet
          (Iff
            (Elem (Var 0) (Var 1))
            (Or
              (Equal (Var 0) (Var 3))
              (Equal (Var 0) (Var 2)))))
  |}.

(* The existence proof declaration states that some set is a pair of a and b.   *)
Definition Exists : DeclP :=
  let concl :=
    (Ex VarTySet
      (App
        (IdentT "IsPairOf" [Var 2; Var 1])
        (Var 0)))
  in
    {| paraP := [TySet; TySet]
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* The uniqueness proof declaration states that any two such sets are equal.    *)
Definition Unique : DeclP :=
  let concl :=
    (All VarTySet
      (All VarTySet
        (Imp
          (App
            (IdentT "IsPairOf" [Var 3; Var 2])
             (Var 1))
          (Imp
            (App
              (IdentT "IsPairOf" [Var 3; Var 2])
              (Var 0))
            (Equal (Var 1) (Var 0))))))
  in
    {| paraP := [TySet; TySet]
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* Definition pair (a b:U) : U := Def (IsPairOf a b) exists unique.             *)
Definition pair : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TySet
  ;  bodyT :=
      Def
        (IdentT "IsPairOf" [Var 1; Var 0])
        (IdentP "Exists" [Var 1; Var 0])
        (IdentP "Unique" [Var 1; Var 0])
  |}.


(* A set belongs to a pair exactly when it is one of the selected sets.         *)
Definition Charac : DeclP :=
  let concl :=
    All VarTySet
      (All VarTySet
        (All VarTySet
          (Iff
            (Elem (Var 0) (IdentT "pair" [Var 2; Var 1]))
            (Or
              (Equal (Var 0) (Var 2))
              (Equal (Var 0) (Var 1))))))
  in
    {| paraP := []
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* The left selected set belongs to its pair.                                   *)
Definition IsInL : DeclP :=
  let concl :=
    All VarTySet
      (All VarTySet
        (Elem (Var 1) (IdentT "pair" [Var 1; Var 0])))
  in
    {| paraP := []
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* The right selected set belongs to its pair.                                  *)
Definition IsInR : DeclP :=
  let concl :=
    All VarTySet
      (All VarTySet
        (Elem (Var 0) (IdentT "pair" [Var 1; Var 0])))
  in
    {| paraP := []
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* Containment of both selected sets is equivalent to class inclusion.          *)
Definition ToClassIncl : DeclP :=
  let concl :=
    All VarTyClass
      (All VarTySet
        (All VarTySet
          (Iff
            (And
              (App (Var 2) (Var 1))
              (App (Var 2) (Var 0)))
            (IdentT "Incl"
              [IdentT "toClass" [IdentT "pair" [Var 1; Var 0]]; Var 2]))))
  in
    {| paraP := []
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Equiv.exports
  ; Incl.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ ("IsPairOf"%string  , IsPairOf)
      ; ("pair"%string      , pair)
      ]
  ; Env.fromListP
      [ ("Exists"%string     , Exists)
      ; ("Unique"%string     , Unique)
      ; ("Charac"%string     , Charac)
      ; ("IsInL"%string      , IsInL)
      ; ("IsInR"%string      , IsInR)
      ; ("ToClassIncl"%string, ToClassIncl)
      ]
  ].

Definition env : Env := Env.union imports exports.
