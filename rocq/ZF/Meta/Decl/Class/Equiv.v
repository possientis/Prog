Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.



(* toClass a x <-> x :< a.                                                      *)
Definition toClass : DeclT :=
  {| paraT := [TySet]
  ;  resT  := TyClass
  ;  bodyT := Lam (Elem (Var 0) (Var 1))
  |}.

(* equiv P Q <-> forall x, P x <-> Q x.                                         *)
Definition equiv : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      All
        (Iff
          (App (Var 2) (Var 0))
          (App (Var 1) (Var 0)))
  |}.



(* forall P, equiv P P.                                                         *)
Definition Refl : DeclP :=
  let concl :=
    IdentT (Name.local "equiv") (args [Var 0; Var 0])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C D, equiv A C -> equiv B D -> equiv A B -> equiv C D.            *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 1]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 2; Var 0]))
        (Imp
          (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
          (IdentT (Name.local "equiv") (args [Var 1; Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, equiv A C -> equiv A B -> equiv C B.                           *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 0]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
        (IdentT (Name.local "equiv") (args [Var 0; Var 1])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B C, equiv B C -> equiv A B -> equiv A C.                           *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
        (IdentT (Name.local "equiv") (args [Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, equiv P Q -> equiv Q P.                                          *)
Definition Sym : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv") (args [Var 0; Var 1]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> equiv Q R -> equiv P R.                           *)
Definition Tran : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (IdentT (Name.local "equiv") (args [Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, ~ equiv P Q -> ~ equiv Q P.                                      *)
Definition NotSym : DeclP :=
  let concl :=
    Imp
      (Not (IdentT (Name.local "equiv") (args [Var 1; Var 0])))
      (Not (IdentT (Name.local "equiv") (args [Var 0; Var 1])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, a = b <-> equiv (toClass a) (toClass b).                         *)
Definition EqualToClass : DeclP :=
  let concl :=
      All
        (All
          (Iff
            (Equal (Var 1) (Var 0))
            (IdentT (Name.local "equiv")
              (args [IdentT (Name.local "toClass") (args [Var 1]);
               IdentT (Name.local "toClass") (args [Var 0])]))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, a <> b <-> ~ equiv (toClass a) (toClass b).                      *)
Definition NotEqualToClass : DeclP :=
  let concl :=
      All
        (All
          (Iff
            (NotEq (Var 1) (Var 0))
            (Not
              (IdentT (Name.local "equiv")
                (args [IdentT (Name.local "toClass") (args [Var 1]);
                 IdentT (Name.local "toClass") (args [Var 0])])))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R S, equiv P Q -> equiv R S -> ~ equiv P R -> ~ equiv Q S.        *)
Definition NotCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (Imp
          (Not (IdentT (Name.local "equiv") (args [Var 3; Var 1])))
          (Not (IdentT (Name.local "equiv") (args [Var 2; Var 0])))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> ~ equiv P R -> ~ equiv Q R.                       *)
Definition NotCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (Imp
        (Not (IdentT (Name.local "equiv") (args [Var 2; Var 0])))
        (Not (IdentT (Name.local "equiv") (args [Var 1; Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> ~ equiv R P -> ~ equiv R Q.                       *)
Definition NotCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (Imp
        (Not (IdentT (Name.local "equiv") (args [Var 0; Var 2])))
        (Not (IdentT (Name.local "equiv") (args [Var 0; Var 1]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.empty.

Definition exports : Env := Env.unions
  [ Env.fromListT
    [ (Name.local "toClass", toClass)
    ; (Name.local "equiv"  , equiv)
    ]
  ; Env.fromListP
    [ (Name.local "Refl"           , Refl)
    ; (Name.local "EquivCompat"    , EquivCompat)
    ; (Name.local "EquivCompatL"   , EquivCompatL)
    ; (Name.local "EquivCompatR"   , EquivCompatR)
    ; (Name.local "Sym"            , Sym)
    ; (Name.local "Tran"           , Tran)
    ; (Name.local "NotSym"         , NotSym)
    ; (Name.local "EqualToClass"   , EqualToClass)
    ; (Name.local "NotEqualToClass", NotEqualToClass)
    ; (Name.local "NotCompat"      , NotCompat)
    ; (Name.local "NotCompatL"     , NotCompatL)
    ; (Name.local "NotCompatR"     , NotCompatR)
    ]
  ].

Definition env : Env := Env.union imports exports.
