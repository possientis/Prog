Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* forall a b, (forall x, x :< a <-> x :< b) -> a = b                           *)
Definition Extensionality : DeclP :=
  let concl :=
      All VarTySet
        (All VarTySet
          (Imp
            (All VarTySet
              (Iff (Elem (Var 0) (Var 2))
                   (Elem (Var 0) (Var 1))))
            (Equal (Var 1) (Var 0))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := AxiomP concl
    |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListP
  [ ("Extensionality"%string, Extensionality)
  ].

Definition env : Env := Env.union imports exports.
