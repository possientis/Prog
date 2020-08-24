Require Import List.

Require Import Logic.Class.Eq.
Require Import Logic.Axiom.LEM.

Require Import Logic.Func.Replace.
Require Import Logic.Func.Composition.

Require Import Logic.Fol.Free.
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

Lemma evalFunctionalF : LEM -> forall (e:Env) (P:Formula) (n m m':nat),
    valid (replace2 0 1 n m)  P ->
    valid (replace2 0 1 n m') P ->
    n <> m  ->
    n <> m' ->
    m <> m' ->
    ~In n  (Fr P) ->
    ~In m  (Fr P) ->
    ~In m' (Fr P) ->
    eval e (functionalF P n m m')
        <->
    functional (eval2 e P 0 1).
Proof.
    intros L e P n m m' H1 H2 H3 H4 H5 H3' H4' H5'. 
    unfold functional, functionalF, eval2. rewrite evalAll.
    split; intros H6 x.
    - intros y y' H7 H8. 
      remember (H6 x)  as H9 eqn:E. clear E H6. rewrite evalAll in H9.
      remember (H9 y)  as H6 eqn:E. clear E H9. rewrite evalAll in H6.
      remember (H6 y') as H9 eqn:E. clear E H6. rewrite evalImp in H9.
      rewrite evalImp in H9. rewrite evalEqu in H9.
      rewrite bindDiff in H9. rewrite bindSame in H9. rewrite bindSame in H9.
      apply H9.
        + apply evalApplyF1; assumption. 
        + apply evalApplyF2; assumption.
        + auto.
        + assumption.
    - rewrite evalAll. intros y. rewrite evalAll. intros y'. 
      rewrite evalImp, evalImp, evalEqu, bindDiff, bindSame, bindSame.
      intros H7 H8. apply H6 with x.
        + rewrite <- evalApplyF1; try (exact H7); assumption.
        + rewrite <- evalApplyF2; try (exact H8); assumption.
        + auto.
        + assumption.
Qed.

(*
Definition replacementF (P:Formula) (n m m' k l:nat) : Formula := Imp 
    (functionalF P n m m')
    (All n (Exi m (All k (Iff (Elem k m) (Exi l (And (Elem l n 
*)
