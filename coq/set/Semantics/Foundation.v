Require Import Core.LEM.
Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Syntax.
Require Import Core.Semantics.
Require Import Core.Environment.

(* Lemma 'coherence' expressed in set theory abstract syntax.                   *)
(* This formulation is correct provided the variables n m are distinct.         *)
Definition coherenceF (n m:nat) : Formula :=
    All n (All m (Imp (Sub n m) (Not (Elem m n)))).


(* Evaluating coherenceF in any environment 'yields' the lemma coherence.       *)
Lemma evalCoherenceF : LEM -> forall (e:Env) (n m:nat),
    m <> n ->
    eval e (coherenceF n m)
        <->
    forall (x y:set), x <== y -> ~ y :: x.
Proof.
    intros L e n m Hmn. unfold coherenceF. rewrite evalAll. split; intros H x.
    - remember (H x)  as H' eqn:E. clear E H.  rewrite evalAll in H'. intros y.
      remember (H' y) as H  eqn:E. clear E H'. rewrite evalImp in H. 
      rewrite evalSub in H. rewrite evalNot in H. rewrite evalElem in H.
      rewrite bindSame in H. rewrite bindDiff in H. rewrite bindSame in H.
        + assumption.
        + assumption.
        + assumption.
    - rewrite evalAll. intros y. rewrite evalImp, evalSub, evalNot, evalElem.
      rewrite bindSame, bindDiff, bindSame. apply H.
        + assumption.
        + assumption.
Qed.

