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

(* Argument lookup agrees with reversed list lookup when it succeeds.           *)
Proposition ArgTNth :
  forall (args:list Term) (n:nat) (t:Term),
    nth_error (rev args) n = Some t           ->
    argT args n = t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros args n t H1. unfold argT. rewrite H1. reflexivity.
Qed.

(* Argument lookup past the supplied arguments returns a remaining variable.    *)
Proposition ArgTVar :
  forall (args:list Term) (n:nat),
    length args <= n                          ->
    argT args n = Var (n - length args).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros args n H1.
  unfold argT.
  (* Past the length of the reversed argument list, lookup must fail.           *)
  assert (nth_error (rev args) n = None) as H2. {
    apply nth_error_None. rewrite length_rev. assumption.
  }
  rewrite H2. reflexivity.
Qed.


