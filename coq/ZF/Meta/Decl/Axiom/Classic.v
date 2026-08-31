Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* ~~A -> A.                                                                    *)
Definition DoubleNegation : DeclP :=
  let concl :=
    Imp
      (Not (Not (Var 0)))
      (Var 0)
  in
    {| paraP  := [TyProp]
    ;  conclP := concl
    ;  bodyP  := AxiomP concl
    |}.

(* not (forall x, P x) iff exists x, not P x.                                   *)
Definition NotForAll : DeclP :=
  let concl :=
    Iff
      (Not
        (All
          (App (Var 1) (Var 0))))
      (Ex
        (Not
          (App (Var 1) (Var 0))))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* not (forall x, not P x) iff exists x, P x.                                   *)
Definition NotForAllNot : DeclP :=
  let concl :=
    Iff
      (Not
        (All
          (Not
            (App (Var 1) (Var 0)))))
      (Ex
        (App (Var 1) (Var 0)))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* A or not A.                                                                  *)
Definition LawExcludedMiddle : DeclP :=
  let concl :=
    Or
      (Var 0)
      (Not (Var 0))
  in
    {| paraP  := [TyProp]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListP
  [ ("DoubleNegation"%string    , DoubleNegation)
  ; ("NotForAll"%string         , NotForAll)
  ; ("NotForAllNot"%string      , NotForAllNot)
  ; ("LawExcludedMiddle"%string , LawExcludedMiddle)
  ].

Definition env : Env := Env.union imports exports.
