Require Import Core.LEM.
Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Syntax.
Require Import Core.Semantics.
Require Import Core.Environment.

(* Theorem 'pairing' expressed in set theory abstract syntax.                   *)
(* This formulation is correct provided the variables n m p q are distinct.     *)
Definition pairingF (n m p q:nat) : Formula :=
    All n (All m (Exi p (All q (Iff (Elem q p) (Or (Equ q n) (Equ q m)))))).

(* Evaluating pairingF in any environment 'yields' the theorem pairing.         *)
Lemma evalPairingF : LEM -> forall (e:Env) (n m p q:nat),
    m <> n ->
    p <> n ->
    p <> m ->
    q <> n ->
    q <> m ->
    q <> p ->
    eval e (pairingF n m p q)
        <->
    forall (x y:set), exists (z:set), forall (u:set),
        u :: z <-> (u == x) \/ (u == y).
Proof.
    intros L e n m p q Hmn Hpn Hpm Hqn Hqm Hqp. unfold pairingF.
    rewrite evalAll. split; intros H x.
    - intros y.
      remember (H x)  as H' eqn:E. clear E. clear H.  rewrite evalAll in H'.
      remember (H' y) as H  eqn:E. clear E. clear H'. rewrite evalExi in H.
      destruct H as [z H]. exists z. intros u. rewrite evalAll in H.
      remember (H u)  as H' eqn:E. clear E. clear H. rewrite evalIff in H'.
      rewrite evalOr in H'. rewrite evalElem in H'. 
      rewrite evalEqu in H'. rewrite evalEqu in H'.
      remember (bind e n x)  as e1 eqn:E1.
      remember (bind e1 m y) as e2 eqn:E2.
      remember (bind e2 p z) as e3 eqn:E3.
      rewrite bindSame in H'. rewrite bindDiff in H'. rewrite bindDiff in H'.
      rewrite bindDiff in H'. rewrite E3 in H'. rewrite bindSame in H'.
      rewrite bindDiff in H'. rewrite bindDiff in H'. rewrite E2 in H'.
      rewrite bindSame in H'. rewrite bindDiff in H'. rewrite E1 in H'.
      rewrite bindSame in H'.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
    - rewrite evalAll. intros y. destruct (H x y) as [z H0]. clear H.
      rewrite evalExi. exists z. rewrite evalAll. intros u.
      rewrite evalIff, evalElem, evalOr, evalEqu, evalEqu.
      remember (bind e n x)  as e1 eqn:E1.
      remember (bind e1 m y) as e2 eqn:E2.
      remember (bind e2 p z) as e3 eqn:E3.
      rewrite bindSame, bindDiff, bindDiff, bindDiff, E3, bindSame.
      rewrite bindDiff, bindDiff, E2, bindSame, bindDiff, E1, bindSame.
        + apply H0.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
Qed.


