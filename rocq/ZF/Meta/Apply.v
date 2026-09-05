Require Import Coq.Lists.List.

Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.

Import ListNotations.

(* An argument list selects actual terms for initial de Bruijn variables.       *)
Definition argT (args:Terms) (n:nat) : Term :=
  match nthT (revT args) n with
  | Some t => t
  | None   => Var (n - lengthT args)
  end.

(* Applying a schematic term substitutes its arguments into its body.           *)
Definition applyT (t:Term) (args:Terms) : Term := substT (argT args) t.

(* Argument lookup agrees with reversed argument lookup when it succeeds.       *)
Proposition ArgTNth : forall (args:Terms) (n:nat) (t:Term),
  nthT (revT args) n = Some t               ->
  argT args n = t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros args n t H1. unfold argT. rewrite H1. reflexivity.
Qed.

(* Argument lookup past the supplied arguments returns a remaining variable.    *)
Proposition ArgTVar : forall (args:Terms) (n:nat),
  lengthT args <= n                         ->
  argT args n = Var (n - lengthT args).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros args n H1.
  unfold argT.
  (* Past the length of the reversed argument list, lookup must fail.           *)
  assert (nthT (revT args) n = None) as H2. {
    unfold nthT, lengthT.
    rewrite ToListRevT.
    apply nth_error_None. rewrite length_rev. assumption.
  }
  rewrite H2. reflexivity.
Qed.
