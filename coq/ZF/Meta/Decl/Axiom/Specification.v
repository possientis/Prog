Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* forall P, forall a, exists b, forall x, x :< b <-> x :< a /\ P x             *)
Definition Specification : DeclP :=
  let concl :=
    All
      (Ex
        (All
          (Iff
            (Elem (Var 0) (Var 1))
            (And
              (Elem (Var 0) (Var 2))
              (App (Var 3) (Var 0))))))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListP
  [ ("Specification"%string, Specification)
  ].

Definition env : Env := Env.union imports exports.
