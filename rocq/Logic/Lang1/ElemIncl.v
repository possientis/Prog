Require Import Logic.Axiom.LEM.

Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Elem.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Context.
Require Import Logic.Lang1.SemanCtx.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Environment.

Open Scope Set_Incl_scope.

(* Theorem 'elemIncl' expressed in set theory abstract syntax.                  *)
(* This formulation is correct when variables n m p are distinct.               *)
Definition elemInclF (n m p:nat) : Formula :=
    All n (All m (Iff (Sub n m) (All p (Imp (Elem p n) (Elem p m))))).

Import Semantics.
(* Evaluating elemInclF in any environment 'yields' the theorem elemIncl.       *)
Lemma evalElemInclF : LEM -> forall (e:Env) (n m p:nat), 
    m <> n -> 
    p <> m -> 
    p <> n ->
    eval e (elemInclF n m p) 
        <-> 
    forall (x y:set), x <= y <-> forall (z:set), z :: x -> z :: y. 
Proof.
    intros L e n m p Mmn Hpm Hpn. unfold elemInclF. rewrite evalAll. split; 
    intros H x.
    - remember (H x) as H' eqn:E. clear E. clear H.
      rewrite evalAll in H'. intros y.
      remember (H' y) as H eqn:E. clear E. clear H'.
      rewrite evalIff in H. rewrite evalSub in H.
      rewrite evalAll in H. 
      remember (bind e n x)  as e1 eqn:E1.
      remember (bind e1 m y) as e2 eqn:E2.
      destruct H as [H1 H2]. split; intro H0.
        + intros z. rewrite E2 in H1.
          rewrite bindDiff in H1. rewrite bindSame in H1.
          rewrite E1 in H1. rewrite bindSame in H1.
          remember (H1 H0) as H1' eqn:E. clear E. clear H1.
          remember (H1' z) as H1  eqn:E. clear E. clear H1'.
          rewrite evalImp in H1. rewrite evalElem in H1. rewrite evalElem in H1.
          rewrite <- E1 in H1. rewrite <- E2 in H1.
          rewrite bindSame in H1. rewrite bindDiff in H1. rewrite bindDiff in H1.
          rewrite E2 in H1. rewrite bindSame in H1. rewrite bindDiff in H1.
          rewrite E1 in H1. rewrite bindSame in H1.
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
        + rewrite E2 in H2. rewrite bindSame in H2. rewrite bindDiff in H2.
          rewrite E1 in H2. rewrite bindSame in H2. apply H2.
          intros z. rewrite evalImp, evalElem, evalElem, <- E1, <- E2.
          rewrite bindSame, bindDiff, bindDiff, E2, bindDiff, bindSame. 
          rewrite E1, bindSame. apply H0.
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
        + assumption. 
    - rewrite evalAll. intros y. rewrite evalIff, evalSub, evalAll.
      remember (bind e n x)  as e1 eqn:E1.
      remember (bind e1 m y) as e2 eqn:E2.
      split; intros H0.
        + intros z. rewrite evalImp, evalElem, evalElem.
          rewrite bindSame, bindDiff, bindDiff. apply H.
            { assumption. }
            { assumption. }
            { assumption. }
        + apply H. intros z.
          remember (H0 z) as H' eqn:E. clear E. clear H0.
          rewrite evalImp in H'. rewrite evalElem in H'. rewrite evalElem in H'.
          rewrite bindSame in H'. rewrite bindDiff in H'. rewrite bindDiff in H'.
            { assumption. }
            { assumption. }
            { assumption. }
        + assumption.
Qed.

Import SemanCtx.
Lemma evalElemInclFCtx : LEM -> forall (G:Context) (n m p:nat), 
    n <> m -> 
    n <> p -> 
    m <> p ->
    G :- (elemInclF n m p) >> 
        forall (x y:set), x <= y <-> forall (z:set), z :: x -> z :: y.
Proof.
    intros L G n m p H1 H2 H3. unfold elemInclF.
    apply evalAll. intros x. apply evalAll. intros y. 
    apply evalIff; try assumption. 
    - apply evalSub; try (apply FindZ). apply FindS; try assumption. apply FindZ.
    - apply evalAll. intros z. apply evalImp; apply evalElem; try (apply FindZ);
      apply FindS; try assumption; try (apply FindZ). 
      apply FindS; try assumption. apply FindZ.
Qed.

