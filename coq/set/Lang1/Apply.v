Require Import List.

Require Import Utils.Replace.
Require Import Utils.Composition.

Require Import Core.Set.
Require Import Core.Equal.

Require Import Lang1.Valid.
Require Import Lang1.Syntax.
Require Import Lang1.Semantics.
Require Import Lang1.Relevance.
Require Import Lang1.Environment.
Require Import Lang1.Substitution.

(* A formula with a free variable could be viewed as a predicate which needs to *)
(* be 'evaluated' at some variable, where such evaluation corresponds to a      *)
(* variable substitution. In the following, we formalize this evaluation by     *)
(* substituting the variable '0' by the argument 'n'. This choice of variable   *)
(* '0' is arbitrary, but having this default choice leads to simpler syntax as  *)
(* there is no need to spell out which variable is being replaced. There is     *)
(* nothing deep here, as we are just creating a new formula from an old one.    *)
(* The ability to apply a formula viewed as predicate to variables is important *)
(* for two variables, and is needed to express the axiom schema of replacement. *)

Definition apply (p:Formula) (n:nat) : Formula := fmap (replace 0 n) p.

Notation "p $ n" := (apply p n) (at level 60, right associativity) : set_scope.

Open Scope set_scope.

(* Semantics of (p $ n) in an environement where n is bound to set x is the     *)
(* same as the semantics of p in an environment where 0 is bound to x. However, *)
(* we cannot hope to obtain this semantics equivalence without assuming that    *)
(* the replacement of variable 0 by n is a valid substitution for p, and that   *)
(* n is not already a free variable in p.                                       *)

(*
Lemma evalApply1 : forall (e:Env) (p:Formula) (n:nat) (x:set),
    Valid (replace 0 n) p ->
    ~In n (free p)        ->
    eval1 e (p $ n) n x <-> eval1 e p 0 x.
Proof.
    unfold eval1, apply. intros e p n x H1 H2. rewrite Substitution.
    apply relevance. intros m.
Show.
*)
