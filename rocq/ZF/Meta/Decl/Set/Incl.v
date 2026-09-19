Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.

(* Incl a b <-> forall x, x :< a -> x :< b.                                     *)
Definition Incl : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TyProp
  ;  bodyT :=
      All
        (Imp
          (Elem (Var 0) (Var 2))
          (Elem (Var 0) (Var 1)))
  |}.

(* forall a b, Incl a b -> CIN.Incl (toClass a) (toClass b).              *)
Definition ToClass : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (IdentT (Name.qualified "CIN" "Incl")
        (args [IdentT (Name.local "toClass") (args [Var 1]);
         IdentT (Name.local "toClass") (args [Var 0])]))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, CIN.Incl (toClass a) (toClass b) -> Incl a b.              *)
Definition FromClass : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.qualified "CIN" "Incl")
        (args [IdentT (Name.local "toClass") (args [Var 1]);
         IdentT (Name.local "toClass") (args [Var 0])]))
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, a = b <-> Incl a b /\ Incl b a.                                  *)
Definition Double : DeclP :=
  let concl :=
    Iff
      (Equal (Var 1) (Var 0))
      (And
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl") (args [Var 0; Var 1])))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, Incl a a.                                                          *)
Definition Refl : DeclP :=
  let concl :=
    IdentT (Name.local "Incl") (args [Var 0; Var 0])
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, Incl a b -> Incl b a -> a = b.                                   *)
Definition Anti : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
        (Equal (Var 1) (Var 0)))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b c, Incl a b -> Incl b c -> Incl a c.                              *)
Definition Tran : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl") (args [Var 2; Var 0])))
  in
    {| paraP  := [TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.qualifyAs "CIN" Incl.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Incl", Incl)
      ]
  ; Env.fromListP
      [ (Name.local "ToClass"  , ToClass)
      ; (Name.local "FromClass", FromClass)
      ; (Name.local "Double"   , Double)
      ; (Name.local "Refl"     , Refl)
      ; (Name.local "Anti"     , Anti)
      ; (Name.local "Tran"     , Tran)
      ]
  ].

Definition env : Env := Env.union imports exports.
