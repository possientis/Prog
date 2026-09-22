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
Require Import ZF.Meta.Decl.Set.Incl.

(* specify P a : U.                                                             *)
Definition specify : DeclT :=
  {| paraT := [TyClass; TySet]
  ;  resT  := TySet
  ;  bodyT :=
      FromC
        (IdentT (Name.local "inter2")
          (args
            [ IdentT (Name.local "toClass") (args [Var 0])
            ; Var 1
            ]))
  |}.

(* forall P a x, x :< specify P a <-> x :< a /\ P x.                            *)
Definition Charac : DeclP :=
  let concl :=
    All
      (Iff
        (Elem (Var 0) (IdentT (Name.local "specify") (args [Var 2; Var 1])))
        (And
          (Elem (Var 0) (Var 1))
          (App (Var 2) (Var 0))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P a, Incl (specify P a) a.                                            *)
Definition IsInclL : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [IdentT (Name.local "specify") (args [Var 1; Var 0]); Var 0])
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P a, CIN.Incl (toClass (specify P a)) P.                              *)
Definition IsInclR : DeclP :=
  let concl :=
    IdentT (Name.qualified "CIN" "Incl")
      (args
        [ IdentT (Name.local "toClass")
            (args [IdentT (Name.local "specify") (args [Var 1; Var 0])])
        ; Var 1
        ])
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P a, CIN.Incl (toClass a) P <-> specify P a = a.                      *)
Definition IsA : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.qualified "CIN" "Incl")
        (args [IdentT (Name.local "toClass") (args [Var 0]); Var 1]))
      (Equal (IdentT (Name.local "specify") (args [Var 1; Var 0])) (Var 0))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.qualifyAs "CIN" ZF.Meta.Decl.Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Incl.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "specify", specify)
      ]
  ; Env.fromListP
      [ (Name.local "Charac"  , Charac)
      ; (Name.local "IsInclL", IsInclL)
      ; (Name.local "IsInclR", IsInclR)
      ; (Name.local "IsA"    , IsA)
      ]
  ].

Definition env : Env := Env.union imports exports.
