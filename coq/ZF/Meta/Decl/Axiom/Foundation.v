Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Inter2.

(* forall a, a <> empty -> exists x, x :< a /\ inter2 x a = empty               *)
Definition Foundation : DeclP :=
  let concl :=
      All VarTySet
        (Imp
          (NotEq (Var 0) (IdentT "empty" []))
          (Ex VarTySet
            (And
              (Elem (Var 0) (Var 1))
              (Equal
                (IdentT "inter2" [Var 0; Var 1])
                (IdentT "empty" [])))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := AxiomP concl
    |}.

Definition imports : Env := Env.unions
  [ Empty.exports
  ; Inter2.exports
  ].

Definition exports : Env := Env.fromListP
  [ ("Foundation"%string, Foundation)
  ].

Definition env : Env := Env.union imports exports.
