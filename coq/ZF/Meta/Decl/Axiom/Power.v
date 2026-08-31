Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* forall a, exists b, forall x, x :< b <-> x <= a                              *)
Definition Power : DeclP :=
  let concl :=
      All VarTySet
        (Ex VarTySet
          (All VarTySet
            (Iff
              (Elem (Var 0) (Var 1))
              (Leq (Var 0) (Var 2)))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := AxiomP concl
    |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListP
  [ ("Power"%string, Power)
  ].

Definition env : Env := Env.union imports exports.
