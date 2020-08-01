Require Import Logic.Axiom.LEM.

Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Environment.

(* Lemma 'equalRefl' expressed in set theory abstract syntax.                   *)
Definition equalReflF (n:nat) : Formula := All n (Equ n n).

(* Evaluating equalReflF in any environment 'yields' the lemma equalRefl.       *)
Lemma evalEqualReflF : LEM -> forall (e:Env) (n:nat), 
    eval e (equalReflF n) <-> forall (x:set), x == x.
Proof.
    intros L e n. unfold equalReflF. rewrite evalAll. split; intros H x.
    - remember (H x) as H' eqn:E. clear E. clear H.
      rewrite evalEqu in H'. rewrite bindSame in H'. 
        + assumption.
        + assumption.
    - rewrite evalEqu, bindSame. apply H.
        + assumption.
Qed.

(* Lemma 'equalSym' expressed in set theory abstract syntax.                    *)
(* This formulation is correct when variables n and m are distinct.             *)
Definition equalSymF (n m:nat):Formula:= All n (All m (Imp (Equ n m) (Equ m n))).

(* Evaluating equalSymF in any environment 'yields' the lemma equalSym.         *)
Lemma evalEqualSymF : LEM -> forall (e:Env) (n m:nat), 
    m <> n -> 
    eval e (equalSymF n m) 
        <->     
    forall (x y:set), x == y -> y == x.
Proof.
    intros L e n m Hmn. unfold equalSymF. rewrite evalAll. split; intros H x.
    - intros y.
      remember (H  x) as H' eqn:E. clear E. clear H. rewrite evalAll in H'. 
      remember (H' y) as H  eqn:E. clear E. clear H'.
      rewrite evalImp in H. rewrite evalEqu in H. rewrite evalEqu in H.
      remember (bind e n x) as e1 eqn:E1.
      rewrite bindSame in H. rewrite bindDiff in H. rewrite E1 in H.
      rewrite bindSame in H.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
    - rewrite evalAll. intros y. remember (bind e n x) as e1 eqn:E1.
      rewrite evalImp, evalEqu, evalEqu, bindSame, bindDiff, E1, bindSame.
        + apply H.
        + assumption.
        + assumption.
        + assumption.
Qed.

(* Lemma 'equalTrans' expressed in set theory abstract syntax.                  *)
(* This formulation is correct when variables n m p are distinct.               *)
Definition equalTransF (n m p:nat) : Formula := 
    All n (All m (All p (Imp (Equ n m) (Imp (Equ m p) (Equ n p))))).

(* Evaluating equalTransF in any environment 'yields' the lemma equalTrans.     *)
Lemma evalEqualTransF : LEM -> forall (e:Env) (n m p:nat), 
    m <> n -> 
    p <> m -> 
    p <> n ->
    eval e (equalTransF n m p)
        <-> 
    forall (x y z:set), x == y -> y == z -> x == z.
Proof.
    intros L e n m p Hmn Hpm Hpn. unfold equalTransF. rewrite evalAll. split; 
    intros H x.
    - intros y z.
      remember (H x) as H' eqn:E. clear E. clear H.  rewrite evalAll in H'.
      remember (H' y) as H eqn:E. clear E. clear H'. rewrite evalAll in H.
      remember (H z) as H' eqn:E. clear E. clear H.
      rewrite evalImp in H'. rewrite evalImp in H'.
      rewrite evalEqu in H'. rewrite evalEqu in H'. rewrite evalEqu in H'.
      remember (bind e n x)  as e1 eqn:E1.
      remember (bind e1 m y) as e2 eqn:E2.
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
    - rewrite evalAll. intros y. rewrite evalAll. intros z.
      remember (bind e n x)  as e1 eqn:E1.
      remember (bind e1 m y) as e2 eqn:E2.
      rewrite evalImp, evalImp, evalEqu, evalEqu, evalEqu.
      rewrite bindSame, bindDiff, bindDiff, E2, bindSame, bindDiff, E1.
      rewrite bindSame.
        + apply H.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
Qed.
