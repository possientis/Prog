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
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Prod.
Require Import ZF.Meta.Decl.Class.Relation.Relation.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* restrict R A := inter2 R (prod A A).                                         *)
Definition restrict : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      IdentT (Name.local "inter2")
        (args
          [ Var 1
          ; IdentT (Name.local "prod") (args [Var 0; Var 0])
          ])
  |}.

(* forall R A x y, restricted R A at (x,y) iff x,y in A and R at (x,y).         *)
Definition Charac2 : DeclP :=
  let pair := IdentT (Name.local "ordPair") (args [Var 1; Var 0]) in
  let concl :=
    Iff
      (App (IdentT (Name.local "restrict") (args [Var 3; Var 2])) pair)
      (And
        (App (Var 2) (Var 1))
        (And (App (Var 2) (Var 0)) (App (Var 3) pair)))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall R A, restrict R A is a relation.                                      *)
Definition IsRelation : DeclP :=
  let concl :=
    IdentT (Name.local "Relation")
      (args [IdentT (Name.local "restrict") (args [Var 1; Var 0])])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall R A, restrict R A is included in R.                                   *)
Definition InclR : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [IdentT (Name.local "restrict") (args [Var 1; Var 0]); Var 1])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall R A x y, restricted R A at (x,y) implies x is in A.                   *)
Definition InAL : DeclP :=
  let concl :=
    Imp
      (App
        (IdentT (Name.local "restrict") (args [Var 3; Var 2]))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (App (Var 2) (Var 1))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall R A x y, restricted R A at (x,y) implies y is in A.                   *)
Definition InAR : DeclP :=
  let concl :=
    Imp
      (App
        (IdentT (Name.local "restrict") (args [Var 3; Var 2]))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (App (Var 2) (Var 0))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.
(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Prod.exports
  ; Env.unqualify Relation.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "restrict", restrict)
      ]
  ; Env.fromListP
      [ (Name.local "Charac2"   , Charac2)
      ; (Name.local "IsRelation", IsRelation)
      ; (Name.local "InclR"     , InclR)
      ; (Name.local "InAL"      , InAL)
      ; (Name.local "InAR"      , InAR)
      ]
  ].

Definition env : Env := Env.union imports exports.
