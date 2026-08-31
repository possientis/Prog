Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Term declarations.                                                           *)

(* Definition toClass (a:U) : Class := fun x => x :< a.                         *)
Definition toClass : DeclT :=
  {| paraT := [TySet]
  ;  resT  := TyClass
  ;  bodyT := Lam (Elem (Var 0) (Var 1))
  |}.

(* Definition equiv (P Q:Class) : Prop := forall x, P x <-> Q x.                *)
Definition equiv : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      All VarTySet
        (Iff
          (App (Var 2) (Var 0))
          (App (Var 1) (Var 0)))
  |}.

(* Proof declarations                                                           *)

(* Proposition Refl : forall (P:Class), equiv P P.                              *)
Definition Refl : DeclP :=
  let concl :=
      All VarTyClass
        (IdentT "equiv" [Var 0; Var 0])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition EquivCompat : forall A B C D,                                    *)
(* equiv A C -> equiv B D -> equiv A B -> equiv C D.                            *)
Definition EquivCompat : DeclP :=
  let concl :=
      All VarTyClass
        (All VarTyClass
          (All VarTyClass
            (All VarTyClass
              (Imp
                (IdentT "equiv" [Var 3; Var 1])
                (Imp
                  (IdentT "equiv" [Var 2; Var 0])
                  (Imp
                    (IdentT "equiv" [Var 3; Var 2])
                    (IdentT "equiv" [Var 1; Var 0])))))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition EquivCompatL : forall A B C,                                     *)
(* equiv A C -> equiv A B -> equiv C B.                                         *)
Definition EquivCompatL : DeclP :=
  let concl :=
      All VarTyClass
        (All VarTyClass
          (All VarTyClass
            (Imp
              (IdentT "equiv" [Var 2; Var 0])
              (Imp
                (IdentT "equiv" [Var 2; Var 1])
                (IdentT "equiv" [Var 0; Var 1])))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition EquivCompatR : forall A B C,                                     *)
(* equiv B C -> equiv A B -> equiv A C.                                         *)
Definition EquivCompatR : DeclP :=
  let concl :=
      All VarTyClass
        (All VarTyClass
          (All VarTyClass
            (Imp
              (IdentT "equiv" [Var 1; Var 0])
              (Imp
                (IdentT "equiv" [Var 2; Var 1])
                (IdentT "equiv" [Var 2; Var 0])))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition Sym : forall P Q, equiv P Q -> equiv Q P.                        *)
Definition Sym : DeclP :=
  let concl :=
      All VarTyClass
        (All VarTyClass
          (Imp
            (IdentT "equiv" [Var 1; Var 0])
            (IdentT "equiv" [Var 0; Var 1])))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition Tran : forall P Q R,                                             *)
(* equiv P Q -> equiv Q R -> equiv P R.                                         *)
Definition Tran : DeclP :=
  let concl :=
      All VarTyClass
        (All VarTyClass
          (All VarTyClass
            (Imp
              (IdentT "equiv" [Var 2; Var 1])
              (Imp
                (IdentT "equiv" [Var 1; Var 0])
                (IdentT "equiv" [Var 2; Var 0])))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition NotSym : forall P Q, ~ equiv P Q -> ~ equiv Q P.                 *)
Definition NotSym : DeclP :=
  let concl :=
      All VarTyClass
        (All VarTyClass
          (Imp
            (Not (IdentT "equiv" [Var 1; Var 0]))
            (Not (IdentT "equiv" [Var 0; Var 1]))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition EqualToClass : forall a b,                                       *)
(* a = b <-> equiv (toClass a) (toClass b).                                     *)
Definition EqualToClass : DeclP :=
  let concl :=
      All VarTySet
        (All VarTySet
          (Iff
            (Equal (Var 1) (Var 0))
            (IdentT "equiv"
              [IdentT "toClass" [Var 1]; IdentT "toClass" [Var 0]])))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition NotEqualToClass : forall a b,                                    *)
(* a <> b <-> ~ equiv (toClass a) (toClass b).                                  *)
Definition NotEqualToClass : DeclP :=
  let concl :=
      All VarTySet
        (All VarTySet
          (Iff
            (NotEq (Var 1) (Var 0))
            (Not
              (IdentT "equiv"
                [IdentT "toClass" [Var 1]; IdentT "toClass" [Var 0]]))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition NotCompat : forall P Q R S,                                      *)
(* equiv P Q -> equiv R S -> ~ equiv P R -> ~ equiv Q S.                        *)
Definition NotCompat : DeclP :=
  let concl :=
      All VarTyClass
        (All VarTyClass
          (All VarTyClass
            (All VarTyClass
              (Imp
                (IdentT "equiv" [Var 3; Var 2])
                (Imp
                  (IdentT "equiv" [Var 1; Var 0])
                  (Imp
                    (Not (IdentT "equiv" [Var 3; Var 1]))
                    (Not (IdentT "equiv" [Var 2; Var 0]))))))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition NotCompatL : forall P Q R,                                       *)
(* equiv P Q -> ~ equiv P R -> ~ equiv Q R.                                     *)
Definition NotCompatL : DeclP :=
  let concl :=
      All VarTyClass
        (All VarTyClass
          (All VarTyClass
            (Imp
              (IdentT "equiv" [Var 2; Var 1])
              (Imp
                (Not (IdentT "equiv" [Var 2; Var 0]))
                (Not (IdentT "equiv" [Var 1; Var 0]))))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Proposition NotCompatR : forall P Q R,                                       *)
(* equiv P Q -> ~ equiv R P -> ~ equiv R Q.                                     *)
Definition NotCompatR : DeclP :=
  let concl :=
      All VarTyClass
        (All VarTyClass
          (All VarTyClass
            (Imp
              (IdentT "equiv" [Var 2; Var 1])
              (Imp
                (Not (IdentT "equiv" [Var 0; Var 2]))
                (Not (IdentT "equiv" [Var 0; Var 1]))))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.empty.

Definition exports : Env := Env.unions
  [ Env.fromListT
    [ ("toClass"%string, toClass)
    ; ("equiv"%string  , equiv)
    ]
  ; Env.fromListP
    [ ("Refl"%string           , Refl)
    ; ("EquivCompat"%string    , EquivCompat)
    ; ("EquivCompatL"%string   , EquivCompatL)
    ; ("EquivCompatR"%string   , EquivCompatR)
    ; ("Sym"%string            , Sym)
    ; ("Tran"%string           , Tran)
    ; ("NotSym"%string         , NotSym)
    ; ("EqualToClass"%string   , EqualToClass)
    ; ("NotEqualToClass"%string, NotEqualToClass)
    ; ("NotCompat"%string      , NotCompat)
    ; ("NotCompatL"%string     , NotCompatL)
    ; ("NotCompatR"%string     , NotCompatR)
    ]
  ].

Definition env : Env := Env.union imports exports.
