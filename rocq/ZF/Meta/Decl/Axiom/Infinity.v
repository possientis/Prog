Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Single.
Require Import ZF.Meta.Decl.Set.Union2.

(* exists a, empty :< a /\ forall x, x :< a -> union2 x (single x) :< a         *)
Definition Infinity : DeclP :=
  let concl :=
      Ex
        (And
          (Elem (IdentT (Name.local "empty") (args [])) (Var 0))
          (All
            (Imp
              (Elem (Var 0) (Var 1))
              (Elem
                (IdentT (Name.local "union2")
                  (args [Var 0; IdentT (Name.local "single") (args [Var 0])]))
                (Var 1)))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := AxiomP concl
    |}.

Definition imports : Env := Env.unions
  [ Empty.exports
  ; Single.exports
  ; Union2.exports
  ].

Definition exports : Env := Env.fromListP
  [ (Name.local "Infinity", Infinity)
  ].

Definition env : Env := Env.union imports exports.
