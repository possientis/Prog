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
Require Import ZF.Meta.Decl.Class.Less.
Require Import ZF.Meta.Decl.Class.Prod.
Require Import ZF.Meta.Decl.Class.Proper.
Require Import ZF.Meta.Decl.Class.Russell.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* V x <-> True.                                                                *)
Definition V : DeclT :=
  {| paraT := []
  ;  resT  := TyClass
  ;  bodyT := Lam Top
  |}.

(* forall A, Incl A V.                                                          *)
Definition IsIncl : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [Var 0; IdentT (Name.local "V") (args [])])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P, equiv (inter2 V P) P.                                              *)
Definition Inter2VL : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "inter2")
            (args [IdentT (Name.local "V") (args []); Var 0])
        ; Var 0
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P, equiv (inter2 P V) P.                                              *)
Definition Inter2VR : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "inter2")
            (args [Var 0; IdentT (Name.local "V") (args [])])
        ; Var 0
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proper V.                                                                    *)
Definition IsProper : DeclP :=
  let concl :=
    IdentT (Name.local "Proper")
      (args [IdentT (Name.local "V") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proper (prod V V).                                                           *)
Definition V2IsProper : DeclP :=
  let concl :=
    IdentT (Name.local "Proper")
      (args
        [ IdentT (Name.local "prod")
            (args
              [ IdentT (Name.local "V") (args [])
              ; IdentT (Name.local "V") (args [])
              ])
        ])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Incl (prod P Q) (prod V V).                                      *)
Definition ProdInclV2 : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args
        [ IdentT (Name.local "prod") (args [Var 1; Var 0])
        ; IdentT (Name.local "prod")
            (args
              [ IdentT (Name.local "V") (args [])
              ; IdentT (Name.local "V") (args [])
              ])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Less (prod V V) V.                                                           *)
Definition IsLess : DeclP :=
  let concl :=
    IdentT (Name.local "Less")
      (args
        [ IdentT (Name.local "prod")
            (args
              [ IdentT (Name.local "V") (args [])
              ; IdentT (Name.local "V") (args [])
              ])
        ; IdentT (Name.local "V") (args [])
        ])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Less.exports
  ; Env.unqualify Prod.exports
  ; Env.unqualify Proper.exports
  ; Env.unqualify Russell.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify Empty.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "V", V)
      ]
  ; Env.fromListP
      [ (Name.local "IsIncl"     , IsIncl)
      ; (Name.local "Inter2VL"   , Inter2VL)
      ; (Name.local "Inter2VR"   , Inter2VR)
      ; (Name.local "IsProper"   , IsProper)
      ; (Name.local "V2IsProper" , V2IsProper)
      ; (Name.local "ProdInclV2" , ProdInclV2)
      ; (Name.local "IsLess"     , IsLess)
      ]
  ].

Definition env : Env := Env.union imports exports.
