Require Import Coq.Lists.List.

Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.

Import ListNotations.

(* An argument list selects actual terms for initial de Bruijn variables.       *)
Definition argT (args:list Term) (n:nat) : Term :=
  match nth_error (rev args) n with
  | Some t => t
  | None   => Var (n - length args)
  end.

(* Applying a schematic term substitutes its arguments into its body.           *)
Definition applyT (t:Term) (args:list Term) : Term := substT (argT args) t.
