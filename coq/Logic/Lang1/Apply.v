Require Import List.

Require Import Logic.Class.Eq.

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


Lemma evalApplyF1 : forall (e:Env) (p:Formula) (n m m':nat) (x y y':set),
    n <> m  ->
    n <> m' ->
    m <> m' -> 
    valid (replace2 0 1 n m) p -> 
    ~ In m' (Fr p) ->
    ~ In m  (Fr p) -> 
    ~ In n  (Fr p) ->
    eval (bind (bind (bind e n x) m y) m' y') (apply2 p n m) 
    <->
    eval (bind (bind e 0 x) 1 y) p.
Proof.
    intros e p n m m' x y y' H1 H2 H3 H4 H1' H2' H3'. 
    unfold apply2. rewrite Substitution.   
    remember (bind (bind (bind e n x) m y) m' y'; replace2 0 1 n m)
    as e1 eqn:E1. remember (bind (bind e 0 x) 1 y) as e2 eqn:E2.
    apply (relevance e1 e2).
    - intros k H5. rewrite E1, E2. unfold comp, bind, replace2.
      destruct (eqDec k 0) as [H6|H6] eqn:K0.
        + subst. destruct (eqDec m' n) as [H7|H7].
            { subst. exfalso. apply H2. reflexivity. }
            { destruct (eqDec m n) as [H8|H8].
                { subst. exfalso. apply H1. reflexivity. }
                { simpl. destruct (PeanoNat.Nat.eq_dec n n) as [H9|H9].
                    { apply equalRefl. }
                    { exfalso. apply H9. reflexivity. }}}
        + destruct (eqDec k 1) as [H7|H7] eqn:K1.
            { subst. destruct (eqDec m' m) as [H7|H7].
                { subst. exfalso. apply H3. reflexivity. }
                { simpl. destruct (PeanoNat.Nat.eq_dec m m) as [H8|H8].
                    { apply equalRefl. }
                    { exfalso. apply H8. reflexivity. }}}
            { destruct (eqDec m' k) as [H8|H8].
                { subst. exfalso. apply H1'. assumption. }
                { destruct (eqDec m k) as [H9|H9].
                    { subst. exfalso. apply H2'. assumption. }
                    { destruct (eqDec n k) as [H10|H10].
                        { subst. exfalso. apply H3'. assumption. }
                        { destruct (eqDec 0 k) as [H11|H11];
                          destruct (eqDec 1 k) as [H12|H12].
                            { subst. inversion H12. }
                            { exfalso. apply H6. symmetry. assumption. }
                            { exfalso. apply H7. symmetry. assumption. }
                            { apply equalRefl. }}}}}
    - assumption.
Qed.


Lemma evalApplyF2 : forall (e:Env) (p:Formula) (n m m':nat) (x y y':set),
    n <> m  ->
    n <> m' ->
    m <> m' -> 
    valid (replace2 0 1 n m') p -> 
    ~ In m' (Fr p) ->
    ~ In m  (Fr p) -> 
    ~ In n  (Fr p) ->
    eval (bind (bind (bind e n x) m y) m' y') (apply2 p n m') 
    <->
    eval (bind (bind e 0 x) 1 y') p.
Proof.
    intros e p n m m' x y y' H1 H2 H3 H4 H1' H2' H3'. 
    remember (bind (bind (bind e n x) m y) m' y') as e1 eqn:E1.
    remember (bind (bind (bind e n x) m' y') m y) as e2 eqn:E2.
    remember (bind (bind e 0 x) 1 y') as e3 eqn:E3.
    assert (envEqual e1 e2) as H5.
        { rewrite E1, E2. apply bindPermute. 
          intros H5. apply H3. symmetry. assumption. }
    assert (eval e1 (apply2 p n m') <-> eval e2 (apply2 p n m')) as H6.
        { apply evalEnvEqual. assumption. }
    rewrite H6, E2, E3. apply evalApplyF1; try (assumption).
    intros H7.  apply H3. symmetry. assumption.
Qed.

