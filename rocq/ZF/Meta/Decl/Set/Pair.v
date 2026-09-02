Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.



(* IsPairOf a b x <-> forall y, y :< x <-> y = a \/ y = b.                      *)
Definition IsPairOf : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (All
          (Iff
            (Elem (Var 0) (Var 1))
            (Or
              (Equal (Var 0) (Var 3))
              (Equal (Var 0) (Var 2)))))
  |}.

(* forall a b, exists x, IsPairOf a b x.                                        *)
Definition Exists : DeclP :=
  let concl :=
    (Ex
      (App
        (IdentT (Name.local "IsPairOf") [Var 2; Var 1])
        (Var 0)))
  in
    {| paraP := [TySet; TySet]
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* forall a b x y, IsPairOf a b x -> IsPairOf a b y -> x = y.                   *)
Definition Unique : DeclP :=
  let concl :=
    (All
      (All
        (Imp
          (App
            (IdentT (Name.local "IsPairOf") [Var 3; Var 2])
             (Var 1))
          (Imp
            (App
              (IdentT (Name.local "IsPairOf") [Var 3; Var 2])
              (Var 0))
            (Equal (Var 1) (Var 0))))))
  in
    {| paraP := [TySet; TySet]
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* IsPairOf a b (pair a b).                                                     *)
Definition pair : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TySet
  ;  bodyT :=
      Def
        (IdentT (Name.local "IsPairOf") [Var 1; Var 0])
        (IdentP (Name.local "Exists") [Var 1; Var 0])
        (IdentP (Name.local "Unique") [Var 1; Var 0])
  |}.


(* forall a b x, x :< pair a b <-> x = a \/ x = b.                              *)
Definition Charac : DeclP :=
  let concl :=
    All
      (All
        (All
          (Iff
            (Elem (Var 0) (IdentT (Name.local "pair") [Var 2; Var 1]))
            (Or
              (Equal (Var 0) (Var 2))
              (Equal (Var 0) (Var 1))))))
  in
    {| paraP := []
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* forall a b, a :< pair a b.                                                   *)
Definition IsInL : DeclP :=
  let concl :=
    All
      (All
        (Elem (Var 1) (IdentT (Name.local "pair") [Var 1; Var 0])))
  in
    {| paraP := []
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* forall a b, b :< pair a b.                                                   *)
Definition IsInR : DeclP :=
  let concl :=
    All
      (All
        (Elem (Var 0) (IdentT (Name.local "pair") [Var 1; Var 0])))
  in
    {| paraP := []
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* forall A a b, A a /\ A b <-> Incl (toClass (pair a b)) A.                    *)
Definition ToClassIncl : DeclP :=
  let concl :=
    All
      (All
        (Iff
          (And
            (App (Var 2) (Var 1))
            (App (Var 2) (Var 0)))
          (IdentT (Name.local "Incl")
            [IdentT (Name.local "toClass")
              [IdentT (Name.local "pair") [Var 1; Var 0]];
             Var 2])))
  in
    {| paraP := [TyClass]
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
      [ (Name.local "IsPairOf"  , IsPairOf)
      ; (Name.local "pair"      , pair)
      ]
  ; Env.fromListP
      [ (Name.local "Exists"     , Exists)
      ; (Name.local "Unique"     , Unique)
      ; (Name.local "Charac"     , Charac)
      ; (Name.local "IsInL"      , IsInL)
      ; (Name.local "IsInR"      , IsInR)
      ; (Name.local "ToClassIncl", ToClassIncl)
      ]
  ].

Definition env : Env := Env.union imports exports.
