Require Import Logic.Axiom.LEM.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Environment.

(* Theorem 'emptySet' expressed in set theory abstract syntax.                  *)
(* This formulation is correct provided the variable names n m are distinct.    *)
Definition emptySetF (n m:nat) : Formula := Exi n (All m (Not (Elem m n))).

(* Evaluating emptySetF in any environment 'yields' the theorem emptySet.       *)
Lemma evalEmptySetF : LEM -> forall (e:Env) (n m:nat),
    m <> n ->
    eval e (emptySetF n m) 
        <->
    exists (x:set), forall (z:set), ~ (z :: x).
Proof.
    intros L e n m Hmn. unfold emptySetF. rewrite evalExi. 
    split; intros [x H]; exists x.
    - intros z. rewrite evalAll in H.
      remember (H z) as H' eqn:E. clear E. clear H.
      rewrite evalNot in H'. rewrite evalElem in H'.
      rewrite bindSame in H'. rewrite bindDiff in H'. rewrite bindSame in H'.
        + assumption.
        + assumption.
    - rewrite evalAll. intros z. rewrite evalNot, evalElem.
      rewrite bindSame, bindDiff, bindSame. 
        + apply H.
        + assumption. 
    - assumption.
Qed.

(* An approximation of lemma 'emptyCharac' expressed in set theory syntax.      *)
(* This formulation is correct when variables n and m are distinct.             *)
Definition emptyCharacF (n m:nat) : Formula :=
        All n (Imp (Empty n) (All m (Not (Elem m n)))).


(* Evaluating emptyCharacF in any environment 'yields' the lemma.               *)
Lemma evalEmptyCharacF : forall (e:Env) (n m:nat),
        m <> n ->
        eval e (emptyCharacF n m)
            <->
        forall (x:set), x == Nil -> forall (y:set), ~ (y :: x).
Proof.
    intros e n m Hmn. unfold emptyCharacF. rewrite evalAll. split; intros H x.
    - remember (H x) as H' eqn:E. clear E H. rewrite evalImp in H'.
      rewrite evalEmpty in H'. rewrite bindSame in H'. rewrite evalAll in H'.
      intros H y. remember (H' H) as H0 eqn:E. clear E H'.
      remember (H0 y) as H' eqn:E. clear E H0. rewrite evalNot in H'.
      rewrite evalElem in H'. rewrite bindSame in H'.
      rewrite bindDiff in H'. rewrite bindSame in H'.
        + assumption.
        + assumption.
    - rewrite evalImp, evalEmpty, bindSame, evalAll. intros H' y.
      rewrite evalNot, evalElem, bindSame, bindDiff, bindSame. apply H.
        + assumption.
        + assumption.
Qed.
