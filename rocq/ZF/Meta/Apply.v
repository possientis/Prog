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
Definition applyT (t:Term) (ts:Terms) : Term := substT (argT ts) t.

(* Argument lookup agrees with reversed argument lookup when it succeeds.       *)
Proposition ArgTNth : forall (ts:Terms) (n:nat) (t:Term),
  nthT (revT ts) n = Some t               ->
  argT ts n = t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts n t H1. unfold argT. rewrite H1. reflexivity.
Qed.

(* Substitution preserves argument lookup when the lookup selects an argument.  *)
Proposition ArgTFromTsNth : forall (ts:Terms) (i:nat) (r:nat -> Term)
  (n:nat) (t:Term),
  nthT (revT ts) n = Some t               ->
  argT (fromTs i r ts) n = fromT i r t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts i r n t H1.
  unfold argT.
  (* The reversed substituted list has the substituted selected argument.       *)
  assert (nthT (revT (fromTs i r ts)) n = Some (fromT i r t)) as H2. {
    rewrite <- RevT. apply NthT. assumption. }
  rewrite H2. reflexivity.
Qed.

(* Argument lookup past the supplied arguments returns a remaining variable.    *)
Proposition ArgTVar : forall (ts:Terms) (n:nat),
  lengthT ts <= n                         ->
  argT ts n = Var (n - lengthT ts).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts n H1.
  unfold argT.
  (* Past the length of the reversed argument list, lookup must fail.           *)
  assert (nthT (revT ts) n = None) as H2. {
    unfold nthT, lengthT.
    rewrite ToListRevT.
    apply nth_error_None. rewrite length_rev. assumption.
  }
  rewrite H2. reflexivity.
Qed.
