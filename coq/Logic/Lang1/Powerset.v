Require Import Logic.Axiom.LEM.

Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Equal.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Environment.

(* Theorem 'powerset' expressed in set theory abstract syntax.                  *)
(* This formulation is correct provided the variables n m p are distinct.       *)

Definition powersetF (n m p:nat) : Formula :=
    All n (Exi m (All p (Iff (Elem p m) (Sub p n)))).


(* Evaluating powersetF in any environment 'yields' the theorem powerset.       *)
Lemma evalpowersetF : LEM -> forall (e:Env) (n m p:nat),
    m <> n ->
    p <> n ->
    p <> m ->
    eval e (powersetF n m p)
        <->
    forall (x:set), exists (y:set), forall (z:set),
        z :: y <-> z <= x.
Proof.
    intros L e n m p Hmn Hpn Hpm. unfold powersetF. rewrite evalAll.
    split; intros H x.
    - remember (H x) as H' eqn:E. clear E. clear H.
      rewrite evalExi in H'. destruct H' as [y H]. exists y. intros z.
      rewrite evalAll in H. remember (H z) as H' eqn:E. clear E. clear H.
      rewrite evalIff in H'. rewrite evalElem in H'. rewrite evalSub in H'.
      remember (bind e n x) as e1 eqn:E1. remember (bind e1 m y) as e2 eqn:E2.
      rewrite bindSame in H'. rewrite bindDiff in H'. rewrite bindDiff in H'.
      rewrite E2 in H'. rewrite bindSame in H'. rewrite bindDiff in H'.
      rewrite E1 in H'. rewrite bindSame in H'.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
    - destruct (H x) as [y H']. rewrite evalExi. exists y. rewrite evalAll.
      intros z. rewrite evalIff, evalElem, evalSub.
      remember (bind e n x) as e1 eqn:E1. remember (bind e1 m y) as e2 eqn:E2.
      rewrite bindSame, bindDiff, bindDiff, E2, bindSame, bindDiff, E1.
      rewrite bindSame. apply H'.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
Qed.
 
