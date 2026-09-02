Require Import Logic.Axiom.LEM.

Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.
Require Import Logic.Set.Foundation.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Context.
Require Import Logic.Lang1.SemanCtx.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Environment.

Open Scope Set_Incl_scope.

(* Lemma 'coherence' expressed in set theory abstract syntax.                   *)
(* This formulation is correct provided the variables n m are distinct.         *)
Definition coherenceF (n m:nat) : Formula :=
    All n (All m (Imp (Sub n m) (Not (Elem m n)))).

Import Semantics.
(* Evaluating coherenceF in any environment 'yields' the lemma coherence.       *)
Lemma evalCoherenceF : forall (e:Env) (n m:nat),
    m <> n ->
    eval e (coherenceF n m)
        <->
    forall (x y:set), x <= y -> ~ y :: x.
Proof.
    intros e n m Hmn. unfold coherenceF. rewrite evalAll. split; intros H x.
    - remember (H x)  as H' eqn:E. clear E H.  rewrite evalAll in H'. intros y.
      remember (H' y) as H  eqn:E. clear E H'. rewrite evalImp in H. 
      rewrite evalSub in H. rewrite evalNot in H. rewrite evalElem in H.
      rewrite bindSame in H. rewrite bindDiff in H. rewrite bindSame in H.
        + assumption.
        + assumption.
    - rewrite evalAll. intros y. rewrite evalImp, evalSub, evalNot, evalElem.
      rewrite bindSame, bindDiff, bindSame. apply H.
        + assumption.
Qed.


Import SemanCtx.
Lemma evalCoherenceFCtx : forall (G:Context) (n m:nat),
    n <> m ->
    G :- (coherenceF n m) >>
        forall (x y:set), x <= y -> ~ y :: x.
Proof.
    intros G n m H1. unfold coherenceF.
    apply evalAll. intros x. apply evalAll. intros y. apply evalImp.
    - apply evalSub.
        + apply FindS; try assumption. apply FindZ.
        + apply FindZ.
    - apply evalNot, evalElem.
        + apply FindZ.
        + apply FindS; try assumption. apply FindZ.
Qed.
 
(* Lemma 'noSelfElem' expressed in set theory abstract syntax.                  *)
Definition noSelfElemF (n:nat) : Formula := All n (Not (Elem n n)).

Import Semantics.
(* Evaluating noSelfElemF in any environment 'yields' the lemma noSelfElem.     *)
Lemma evalNoSelfElemF : forall (e:Env) (n:nat),
    eval e (noSelfElemF n) <-> forall (x:set), ~ x :: x.
Proof.
    intros e n. unfold noSelfElemF. rewrite evalAll. split; intros H x.
    - remember (H x) as H' eqn:E. clear E H. rewrite evalNot in H'.
      rewrite evalElem in H'. rewrite bindSame in H'. assumption.
    - rewrite evalNot, evalElem, bindSame. apply H.
Qed.

Import SemanCtx.
Lemma evalNoSelfElemFCtx : forall (G:Context) (n:nat),
    G :- (noSelfElemF n) >>  forall (x:set), ~ x :: x.
Proof.
    intros G n. unfold noSelfElemF.
    apply evalAll. intros x. apply evalNot, evalElem; apply FindZ.
Qed.


(* Lemma 'noUniverse' expressed in set theory abstract syntax.                  *)
(* This formulation is correct provided the variables n m are distinct.         *)
Definition noUniverseF (n m:nat) : Formula := Not (Exi n (All m (Elem m n))).

Import Semantics.
(* Evaluating noUniverseF in any environment 'yields' the lemma noUniverse.     *)
Lemma evalNoUniverseF : LEM -> forall (e:Env) (n m:nat),
    m <> n ->
    eval e (noUniverseF n m)
        <->
    ~ exists (x:set), forall (y:set), y :: x.
Proof.
    intros L e n m Hmn. unfold noUniverseF. rewrite evalNot, evalExi.
    split; intros H1 [x H2]; apply H1; exists x.
    - rewrite evalAll. intros y. rewrite evalElem, bindSame, bindDiff, bindSame. 
      apply H2. assumption.
    - rewrite evalAll in H2. intros y. remember (H2 y) as H eqn:E. clear E H2 H1.
      rewrite evalElem in H. rewrite bindSame in H. rewrite bindDiff in H.
      rewrite bindSame in H. assumption. assumption.
    - assumption.
Qed.

Import SemanCtx.
Lemma evalNoUniverseFCtx : LEM -> forall (G:Context) (n m:nat),
    n <> m ->
    G :- (noUniverseF n m) >>
        ~ exists (x:set), forall (y:set), y :: x.
Proof.
    intros L G n m H1. unfold noUniverseF.
    apply evalNot, evalExi; try assumption. intros x. apply evalAll. intros y.
    apply evalElem; try (apply FindZ). apply FindS; try assumption. apply FindZ.
Qed.
 

(* Theorem 'foundation' expressed in set theory abstract syntax.                *)
(* This formulation is correct provided the variables n m are distinct.         *)
(* Of course this formulation is somewhat arbitrary as we decided to introduce  *)
(* the builtin predicate 'Min' as part of the language.                         *)
Definition foundationF (n m:nat) : Formula := 
    All n (Imp (Not (Empty n)) (Exi m (Min m n))).

Import Semantics.
(* Evaluating foundationF in any environment 'yields' the theorem foundation.   *)
Lemma evalFoundationF : LEM -> forall (e:Env) (n m:nat),
    m <> n ->
    eval e (foundationF n m) 
        <->
    forall (x:set), ~(x == Nil) -> exists (y:set), minimal y x.
Proof.
    intros L e n m Hmn. unfold foundationF. rewrite evalAll. split; intros H x.
    - remember (H x) as H' eqn:E. clear E H. rewrite evalImp in H'.
      rewrite evalNot in H'. rewrite evalEmpty in H'. rewrite bindSame in H'. 
      intros H. remember (H' H) as H0 eqn:E. clear E H H'.
      rewrite evalExi in H0. destruct H0 as [y H]. exists y.
      rewrite evalMin in H. rewrite bindSame in H. rewrite bindDiff in H.
      rewrite bindSame in H.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
    - rewrite evalImp, evalNot, evalEmpty, bindSame, evalExi.
      remember (H x) as H' eqn:E. clear E H. intros H.
      remember (H' H) as H1 eqn:E. clear E H H'. destruct H1 as [y H].
      exists y. rewrite evalMin, bindSame, bindDiff, bindSame.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
Qed.

Import SemanCtx.
Lemma evalFoundationFCtx : LEM -> forall (G:Context) (n m:nat),
    n <> m ->
    G :- (foundationF n m)  >>
        forall (x:set), ~(x == Nil) -> exists (y:set), minimal y x.
Proof.
    intros L G n m H1. unfold foundationF. 
    apply evalAll. intros x. apply evalImp. 
    - apply evalNot, evalEmpty, FindZ.
    - apply evalExi; try assumption. intros y. apply evalMin; try assumption.
        + apply FindZ.
        + apply FindS; try assumption. apply FindZ.
Qed.
