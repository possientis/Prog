Require Import Logic.Axiom.LEM.

Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Context.
Require Import Logic.Lang1.SemanCtx.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Environment.

Open Scope Set_Incl_scope.

(* Theorem 'pairing' expressed in set theory abstract syntax.                   *)
(* This formulation is correct provided the variables n m p q are distinct.     *)
Definition pairingF (n m p q:nat) : Formula :=
    All n (All m (Exi p (All q (Iff (Elem q p) (Or (Equ q n) (Equ q m)))))).

Import Semantics.
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

Import SemanCtx.
Lemma evalPairingFCtx : LEM -> forall (G:Context) (n m p q:nat),
    n <> m ->
    n <> p ->
    n <> q ->
    m <> p ->
    m <> q ->
    p <> q ->
    G :- (pairingF n m p q) >>
        forall (x y:set), exists (z:set), forall (u:set),
            u :: z <-> (u == x) \/ (u == y).
Proof.
    intros L G n m p q H1 H2 H3 H4 H5 H6. unfold pairingF. 
    apply evalAll. intros x. apply evalAll. intros y.
    apply evalExi; try assumption. intros z. apply evalAll. intros u.
    apply evalIff; try assumption.
    - apply evalElem; try (apply FindZ). apply FindS; try assumption.
      apply FindZ.
    - apply evalOr; try assumption.
        + apply evalEqu; try assumption; try (apply FindZ).
          apply FindS; try assumption. apply FindS; try assumption.
          apply FindS; try assumption. apply FindZ.
        + apply evalEqu; try assumption; try (apply FindZ).
          apply FindS; try assumption. apply FindS; try assumption.
          apply FindZ.
Qed.
