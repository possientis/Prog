Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* forall a b, exists c, forall x, x :< c <-> x = a \/ x = b                    *)
Definition Pairing : DeclP :=
  let concl :=
      All
        (All
          (Ex
            (All
              (Iff
                (Elem (Var 0) (Var 1))
                (Or
                  (Equal (Var 0) (Var 3))
                  (Equal (Var 0) (Var 2)))))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := AxiomP concl
    |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListP
  [ ("Pairing"%string, Pairing)
  ].

Definition env : Env := Env.union imports exports.
