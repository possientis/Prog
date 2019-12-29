Require Import Core.LEM.
Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Syntax.
Require Import Core.Semantics.
Require Import Core.Environment.

(* Theorem 'inclTrans' expressed in set theory abstract syntax.                 *)
(* This formulation is correct when variables n m p are distinct.               *)
Definition inclTransF (n m p:nat) : Formula := 
    All n (All m (All p (Imp (Sub n m) (Imp (Sub m p) (Sub n p))))).

(* Evaluating inclTransF in any environment 'yields' the theorem inclTrans.     *)
Lemma evalTransReflF : LEM -> forall (e:Env) (n m p:nat), 
    m <> n -> 
    p <> m -> 
    p <> n ->
    eval e (inclTransF n m p) 
        <-> 
    forall (x y z:set), x <== y -> y <== z -> x <== z. 
Proof.
    intros L e n m p Hmn Hpm Hpn. unfold inclTransF. rewrite evalAll. split.
    - intros H x y z. 
      remember (H x) as H' eqn:E. clear E. clear H.
      rewrite evalAll in H'.
      remember (H' y) as H eqn:E. clear E. clear H'.
      rewrite evalAll in H.
      remember (H z) as H' eqn:E. clear E. clear H.
      rewrite evalImp in H'. rewrite evalImp in H'.
      rewrite evalSub in H'. rewrite evalSub in H'. rewrite evalSub in H'.
      remember (bind e n x)  as e1 eqn:E1.
      remember (bind e1 m y) as e2 eqn:E2.
      rewrite bindDiff in H'. rewrite bindDiff in H'. rewrite bindSame in H'.
      rewrite E2 in H'. rewrite bindDiff in H'. rewrite bindSame in H'.
      rewrite E1 in H'. rewrite bindSame in H'.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
    - intros H x. rewrite evalAll. intros y. rewrite evalAll. intros z.
      remember (bind e n x)  as e1 eqn:E1.
      remember (bind e1 m y) as e2 eqn:E2.
      remember (bind e2 p z) as e3 eqn:E3.
      rewrite evalImp, evalImp, evalSub, evalSub, evalSub, E3. 
      rewrite bindSame, bindDiff, bindDiff, E2.
      rewrite bindSame, bindDiff, E1, bindSame.
        + apply H.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
Qed.

