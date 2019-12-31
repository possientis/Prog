Require Import Core.LEM.
Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Syntax.
Require Import Core.Semantics.
Require Import Core.Environment.

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
