Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

(* forall a, exists b, forall x, x :< b <-> exists y, x :< y /\ y :< a          *)
Definition Union : DeclP :=
  let concl :=
      All
        (Ex
          (All
            (Iff
              (Elem (Var 0) (Var 1))
              (Ex
                (And
                  (Elem (Var 1) (Var 0))
                  (Elem (Var 0) (Var 3)))))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := AxiomP concl
    |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListP
  [ (Name.local "Union", Union)
  ].

Definition env : Env := Env.union imports exports.
