Require Import Utils.LEM.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Equal.

Require Import Lang1.Syntax.
Require Import Lang1.Semantics.
Require Import Lang1.Environment.

(* Lemma 'inclRefl' expressed in set theory abstract syntax.                    *)
Definition inclReflF (n:nat) : Formula := All n (Sub n n).

(* The intent is to provide some validation to our semantics by going through   *)
(* several key set theoretic results and proving the equivalence between the    *)
(* evaluated abstract syntax and the corresponding Coq statement. However, the  *)
(* value of such exercise is limited as a Coq equivalence 'A <-> B' can always  *)
(* be proved whenever A and B are themselves provable. So 'A <-> B' does not in *)
(* itself prove that the propositions A and B are the 'same'. For our defense,  *)
(* we are proving the equivalence 'A <-> B' without using any result which      *)
(* asserts A or B. In particular, we make no use of the lemma 'inclRefl'.       *)
(* With this caveat in mind, we assert that evaluating inclReflF in any         *)
(* environment (and for any choice of variable name 'n') yields a proposition   *)
(* which is equivalent to the lemma inclRefl.                                   *)
Lemma evalInclReflF : LEM -> forall (e:Env) (n:nat),
    eval e (inclReflF n) <-> forall (x:set), x <== x.
Proof.
    intros L e n. unfold inclReflF. rewrite evalAll. split; intros H x.
    - remember (H x) as H' eqn:E. clear E. 
      rewrite evalSub in H'. 
        + rewrite bindSame in H'. assumption.
        + assumption.
    - rewrite evalSub.
        + rewrite bindSame. apply H.
        + assumption.
Qed.        

(* An approximation of lemma 'inclNil' expressed in set theory abstract syntax. *)
(* This formulation is correct when variables n and m are distinct.             *)
Definition inclNilF (n m:nat) : Formula := 
    All n (Imp (Empty n) (All m (Sub n m))).

(* Evaluating  inclNilF in any environment 'yields' the lemma inclNil.          *)
Lemma evalInclNilF : LEM -> forall (e:Env) (n m:nat), 
    m <> n ->
    eval e (inclNilF n m ) 
        <-> 
    forall (x:set), x == Nil -> forall (y:set), x <== y.
Proof.
    intros L e n m Hmn. unfold inclNilF. rewrite evalAll. split; intros H x.
    - remember (H x) as H' eqn:E. clear E H. rewrite evalImp in H'.
      rewrite evalEmpty in H'. rewrite bindSame in H'. intro H.
      remember (H' H) as H0 eqn:E. clear E H H'. rewrite evalAll in H0.
      intros y. remember (H0 y) as H eqn:E. clear E H0.
      rewrite evalSub in H. rewrite bindSame in H. rewrite bindDiff in H.
      rewrite bindSame in H.
        + assumption.
        + assumption.
        + assumption.
    - rewrite evalImp, evalEmpty, bindSame, evalAll. intros H' y.
      rewrite evalSub, bindSame, bindDiff, bindSame. apply H.
        + assumption.
        + assumption.
        + assumption.
Qed.

