Require Import List.

Require Import Logic.Axiom.LEM.

Require Import Logic.Func.Replace.
Require Import Logic.Func.Composition.

Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Syntax.
Require Import Logic.Fol.Functor.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Equal.
Require Import Logic.Set.Functional.
Require Import Logic.Set.Compatible.

Require Import Logic.Lang1.Apply.
Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Relevance.
Require Import Logic.Lang1.Environment.
Require Import Logic.Lang1.Substitution.

(* A n (A m (A m' (P n m -> P n m' -> m = m')))                                 *)
Definition functionalF (P:Formula) (n m m':nat) : Formula :=
    All n (All m (All m' (Imp (apply2 P n m) (Imp (apply2 P n m') (Equ m m'))))). 

(*
Lemma evalFunctionalF : LEM -> forall (e:Env) (P:Formula) (n m m':nat),
    valid (replace2 0 1 n m)  P ->
    valid (replace2 0 1 n m') P ->
    eval e (functionalF P n m m')
        <->
    functional (eval2 e P 0 1).
Proof.
    intros L e P n m m' H1 H2. 
    unfold functional, functionalF, apply2, eval2. rewrite evalAll.
    split; intros H3 x.
    - intros y y' H4 H5. 
    remember (H3 x)  as H6 eqn:E. clear E H3. rewrite evalAll in H6.
    remember (H6 y)  as H3 eqn:E. clear E H6. rewrite evalAll in H3.
    remember (H3 y') as H6 eqn:E. clear E H3. rewrite evalImp in H6.
    rewrite evalImp in H6. rewrite evalEqu in H6.
    rewrite bindDiff in H6. rewrite bindSame in H6. rewrite bindSame in H6.
    apply H6.
        + apply Substitution.
            { exact H1.     (* <- H1 *) }
            { 
Show.
*)
