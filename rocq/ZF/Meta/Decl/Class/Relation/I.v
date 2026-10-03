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
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Order.Isom.
Require Import ZF.Meta.Decl.Class.Prod.
Require Import ZF.Meta.Decl.Class.Relation.Bij.
Require Import ZF.Meta.Decl.Class.Relation.Bijection.
Require Import ZF.Meta.Decl.Class.Relation.BijectionOn.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Function.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.FunctionOn.
Require Import ZF.Meta.Decl.Class.Relation.OneToOne.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Relation.
Require Import ZF.Meta.Decl.Class.Relation.Restrict.
Require Import ZF.Meta.Decl.Class.V.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* I is the class of all ordered pairs of the form (x,x).                       *)
Definition I : DeclT :=
  {| paraT := []
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (SyntaxT.Equal
            (Var 1)
            (IdentT (Name.local "ordPair") (args [Var 0; Var 0]))))
  |}.

(* forall y z, (y,z) belongs to I iff y equals z.                               *)
Definition Charac2 : DeclP :=
  let concl :=
    Iff
      (App
        (IdentT (Name.local "I") (args []))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (SyntaxT.Equal (Var 1) (Var 0))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I is a functional class.                                                     *)
Definition IsFunctional : DeclP :=
  let concl :=
    IdentT (Name.local "Functional")
      (args [IdentT (Name.local "I") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I is a relation class.                                                       *)
Definition IsRelation : DeclP :=
  let concl :=
    IdentT (Name.local "Relation")
      (args [IdentT (Name.local "I") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I is a function class.                                                       *)
Definition IsFunction : DeclP :=
  let concl :=
    IdentT (Name.local "Function")
      (args [IdentT (Name.local "I") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* The converse of I is I itself.                                               *)
Definition Converse : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "converse")
            (args [IdentT (Name.local "I") (args [])])
        ; IdentT (Name.local "I") (args [])
        ])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I is one-to-one.                                                             *)
Definition IsOneToOne : DeclP :=
  let concl :=
    IdentT (Name.local "OneToOne")
      (args [IdentT (Name.local "I") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I is a bijection class.                                                      *)
Definition IsBijection : DeclP :=
  let concl :=
    IdentT (Name.local "Bijection")
      (args [IdentT (Name.local "I") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* The domain of I is V.                                                        *)
Definition Domain : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "domain")
            (args [IdentT (Name.local "I") (args [])])
        ; IdentT (Name.local "V") (args [])
        ])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* The range of I is V.                                                         *)
Definition Range : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "range")
            (args [IdentT (Name.local "I") (args [])])
        ; IdentT (Name.local "V") (args [])
        ])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I is a function on V.                                                        *)
Definition IsFunctionOn : DeclP :=
  let concl :=
    IdentT (Name.local "FunctionOn")
      (args
        [ IdentT (Name.local "I") (args [])
        ; IdentT (Name.local "V") (args [])
        ])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I is a bijection on V.                                                       *)
Definition IsBijectionOn : DeclP :=
  let concl :=
    IdentT (Name.local "BijectionOn")
      (args
        [ IdentT (Name.local "I") (args [])
        ; IdentT (Name.local "V") (args [])
        ])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I is a bijection from V onto V.                                              *)
Definition IsBij : DeclP :=
  let concl :=
    IdentT (Name.local "Bij")
      (args
        [ IdentT (Name.local "I") (args [])
        ; IdentT (Name.local "V") (args [])
        ; IdentT (Name.local "V") (args [])
        ])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall x, evaluating I at x gives x.                                         *)
Definition Eval : DeclP :=
  let concl :=
    SyntaxT.Equal
      (IdentT (Name.local "eval")
        (args [IdentT (Name.local "I") (args []); Var 0]))
      (Var 0)
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall R, I is an isomorphism from R to itself over V.                       *)
Definition IsIsom : DeclP :=
  let concl :=
    IdentT (Name.local "Isom")
      (args
        [ IdentT (Name.local "I") (args [])
        ; Var 0
        ; Var 0
        ; IdentT (Name.local "V") (args [])
        ; IdentT (Name.local "V") (args [])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Isom.exports
  ; Env.unqualify Prod.exports
  ; Env.unqualify Bij.exports
  ; Env.unqualify Bijection.exports
  ; Env.unqualify BijectionOn.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Function.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify FunctionOn.exports
  ; Env.unqualify OneToOne.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify Relation.exports
  ; Env.unqualify Restrict.exports
  ; Env.unqualify V.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify EvalOfClass.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "I", I)
      ]
  ; Env.fromListP
      [ (Name.local "Charac2"         , Charac2)
      ; (Name.local "IsFunctional"    , IsFunctional)
      ; (Name.local "IsRelation"      , IsRelation)
      ; (Name.local "IsFunction"      , IsFunction)
      ; (Name.local "Converse"        , Converse)
      ; (Name.local "IsOneToOne"      , IsOneToOne)
      ; (Name.local "IsBijection"     , IsBijection)
      ; (Name.local "Domain"          , Domain)
      ; (Name.local "Range"           , Range)
      ; (Name.local "IsFunctionOn"    , IsFunctionOn)
      ; (Name.local "IsBijectionOn"   , IsBijectionOn)
      ; (Name.local "IsBij"           , IsBij)
      ; (Name.local "Eval"            , Eval)
      ; (Name.local "IsIsom"          , IsIsom)
      ]
  ].

Definition env : Env := Env.union imports exports.
