Require Import List.

Require Import Logic.Func.Replace.
Require Import Logic.Func.Composition.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Functor.

Require Import Logic.Set.Set.
Require Import Logic.Set.Equal.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Relevance.
Require Import Logic.Lang1.Environment.
Require Import Logic.Lang1.Substitution.

(* A formula with a free variable could be viewed as a predicate which needs to *)
(* be 'evaluated' at some variable, where such evaluation corresponds to a      *)
(* variable substitution. In the following, we formalize this evaluation by     *)
(* substituting the variable '0' by the argument 'n'. This choice of variable   *)
(* '0' is arbitrary, but having this default choice leads to simpler syntax as  *)
(* there is no need to spell out which variable is being replaced. There is     *)
(* nothing deep here, as we are just creating a new formula from an old one.    *)
(* The ability to apply a formula viewed as predicate to variables is important *)
(* for two variables, and is needed to express the axiom schema of replacement. *)

Definition apply (p:Formula) (n:nat) : Formula := fmap (n // 0) p.

(* Same idea, but with two variables.                                           *)
Definition apply2 (p:Formula) (n m:nat) : Formula := fmap (replace2 0 1 n m) p.

(* The semantics of 'apply p n' in an environement where n is bound to set x    *)
(* is the same as the semantics of p in an environment where 0 is bound to x.   *)
(* However, we cannot hope to obtain this semantics equivalence without         *)
(* assuming that the replacement of variable 0 by n is a valid substitution     *)
(* for p. Also, n cannot already be a free variable of p.                       *)

Lemma evalApply1 : forall (e:Env) (p:Formula) (n:nat) (x:set),
    valid (n // 0) p ->
    ~In n (Fr p)        ->
    eval1 e (apply p n) n x <-> eval1 e p 0 x.
Proof.
    unfold eval1, apply. intros e p n x H1 H2. rewrite Substitution.
    - apply relevance. intros m H3. apply bindReplace. intros H4. 
      subst. apply H2. assumption. 
    - assumption.
Qed.


(* The semantics of 'apply2 p n m' in an environment where n is bound to x and  *)
(* m is bound to y, is the same as the semantics of p in an environment where 0 *)
(* is bound to x and 1 is bound to y, with the obvious caveat.                  *)
Lemma evalApply2 : forall (e:Env) (p:Formula) (n m:nat) (x y:set),
    valid (replace2 0 1 n m) p ->
    ~In n (Fr p)  ->
    ~In m (Fr p)  ->
    n <> m          ->
    eval2 e (apply2 p n m) n m x y <-> eval2 e p 0 1 x y.
Proof.
    unfold eval2, apply2. intros e p n m x y H1 H2 H3 H4. rewrite Substitution.
    - apply relevance. intros r H5. unfold comp. apply bindReplace2.
        + auto.
        + apply H4.                                     (* <- H4 *)
        + intros H6. apply H2. rewrite H6. assumption.  (* <- H2 *)
        + intros H6. apply H3. rewrite H6. assumption.  (* <- H3 *)
    - apply H1.                                         (* <- H1 *)
Qed.
