Require Import Core.LEM.
Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Syntax.
Require Import Core.Semantics.
Require Import Core.Environment.


(* Theorem 'unionAxiom' expressed in set theory abstract syntax.                *)
(* This formulation is correct provided the variables n m p q are distinct.     *)

Definition unionAxiomF (n m p q:nat) : Formula :=
    All n (Exi m (All p (Iff (Elem p m) (Exi q (And (Elem p q) (Elem q n)))))).


(* Evaluating unionAxiomF in any environment 'yields' the theorem unionAxiom.   *)
Lemma evalUnionAxiomF : LEM -> forall (e:Env) (n m p q:nat),
    m <> n ->
    p <> n ->
    p <> m ->
    q <> n ->
    q <> m ->
    q <> p ->
    eval e (unionAxiomF n m p q)
        <->
    forall (x:set), exists (y:set), forall (z:set),
        z :: y <-> exists (u:set), z :: u /\ u :: x. 
Proof.
    intros L e n m p q Hmn Hpn Hpm Hqn Hqm Hqp.
    unfold unionAxiomF. rewrite evalAll. split; intros H x.
    - remember (H x) as H' eqn:E. clear E. clear H. rewrite evalExi in H'.
      destruct H' as [y H]. rewrite evalAll in H. exists y. intros z. 
      remember (H z) as H' eqn:E. clear E. clear H. rewrite evalIff in H'.
      remember (bind e n x) as e1 eqn:E1. remember (bind e1 m y) as e2 eqn:E2.
      rewrite evalElem in H'. rewrite evalExi in H'. rewrite bindSame in H'.
      rewrite bindDiff in H'. destruct H' as [H1 H2]. split; intros H0.
        + rewrite E2 in H1. rewrite bindSame in H1.
          remember (H1 H0) as H3 eqn:E. clear E. clear H1.
          destruct H3 as [u H3]. exists u. rewrite evalAnd in H3.
          rewrite evalElem in H3. rewrite evalElem in H3.
          rewrite <- E2 in H3. remember (bind e2 p z) as e3 eqn:E3.
          rewrite bindSame in H3. rewrite bindDiff in H3. rewrite bindDiff in H3.
          rewrite E3 in H3. rewrite bindSame in H3. rewrite bindDiff in H3.
          rewrite E2 in H3. rewrite bindDiff in H3. rewrite E1 in H3.
          rewrite bindSame in H3.
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }

        + rewrite E2 in H2. rewrite bindSame in H2. apply H2.
          destruct H0 as [u H3]. exists u. rewrite evalAnd, evalElem, evalElem.
          rewrite <- E2. remember (bind e2 p z) as e3 eqn:E3.
          rewrite bindSame, bindDiff, bindDiff, E3, bindSame, bindDiff, E2.
          rewrite bindDiff, E1, bindSame.
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
        + assumption.
        + assumption.
        + assumption.
        + assumption.
    - remember (H x) as H' eqn:E. clear E. clear H. destruct H' as [y H].
      rewrite evalExi. exists y. rewrite evalAll. intros z.
      rewrite evalIff, evalElem, evalExi.
      remember (bind e n x) as e1 eqn:E1. remember (bind e1 m y) as e2 eqn:E2.
      rewrite bindSame, bindDiff, E2, bindSame. split; intros H'.
        + destruct (H z) as [H1 H2]. destruct (H1 H') as [u H3]. exists u.
          rewrite evalAnd, evalElem, evalElem, <- E2.
          remember (bind e2 p z) as e3 eqn:E3.
          rewrite bindSame, bindDiff, E3, bindSame, bindDiff, bindDiff, E2.
          rewrite bindDiff, E1, bindSame.
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
        + destruct (H z) as [H1 H2]. apply H2. destruct H' as [u H3]. exists u.
          rewrite evalAnd in H3. rewrite evalElem in H3. rewrite evalElem in H3.
          rewrite <- E2 in H3. remember (bind e2 p z) as e3 eqn:E3.
          rewrite bindSame in H3. rewrite bindDiff in H3. rewrite bindDiff in H3.
          rewrite E3 in H3. rewrite bindSame in H3. rewrite bindDiff in H3.
          rewrite E2 in H3. rewrite bindDiff in H3. rewrite E1 in H3.
          rewrite bindSame in H3.
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
        + assumption.
        + assumption.
        + assumption.
        + assumption.
Qed.

