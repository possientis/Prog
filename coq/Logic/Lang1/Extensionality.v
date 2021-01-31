Require Import Logic.Axiom.LEM.

Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Context.
Require        Logic.Lang1.SemanCtx.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Environment.

Open Scope Set_Incl_scope.

(* Theorem 'extensionality' expressed in set theory abstract syntax.            *)
(* This formulation is correct provided the variables names n m p are distinct. *)
Definition extensionalityF (n m p:nat) : Formula :=
    All n (All m (Iff (Equ n m) (All p (Iff (Elem p n) (Elem p m))))).

(* Theorem 'doubleIncl' expressed in set theory abstract syntax.                *)
(* This formulation is correct provided the variables names n m are distinct.   *)
Definition doubleInclF (n m:nat) : Formula :=
    All n (All m (Iff (Equ n m) (And (Sub n m) (Sub m n)))).

Import Semantics.
(* Evaluating extensionalityF in any environment 'yields' the theorem.          *)
Lemma evalExtensionalityF : LEM -> forall (e:Env) (n m p:nat),
    m <> n -> 
    p <> m -> 
    p <> n ->
    eval e (extensionalityF n m p)
        <->
    forall (x y:set), x == y <-> forall (z:set), z :: x <-> z :: y. 
Proof.
    intros L e n m p Hmn Hpm Hpn. unfold extensionalityF. rewrite evalAll.
    split; intros H x.
    - intros y. 
      remember (H x)  as H' eqn:E. clear E. clear H. rewrite evalAll in H'.
      remember (H' y) as H  eqn:E. clear E. clear H'.  
      rewrite evalIff in H. rewrite evalEqu in H. rewrite evalAll in H.
      remember (bind e n x) as e1 eqn:E1. rewrite bindDiff in H.
      rewrite bindSame in H. rewrite E1 in H. rewrite bindSame in H.
      destruct H as [H1 H2]. split; intros H.
        + intros z. remember (H1 H z) as H' eqn:E. clear E. clear H.
          rewrite <- E1 in H'. remember (bind e1 m y) as e2 eqn:E2.
          rewrite evalIff in H'. rewrite evalElem in H'. rewrite evalElem in H'.
          rewrite bindSame in H'. rewrite bindDiff in H'. rewrite bindDiff in H'.
          rewrite E2 in H'. rewrite bindSame in H'. rewrite bindDiff in H'.
          rewrite E1 in H'. rewrite bindSame in H'.
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
        + apply H2. intros z. rewrite <- E1. remember (bind e1 m y) as e2 eqn:E2.
          rewrite evalIff, evalElem, evalElem, bindSame, bindDiff, bindDiff, E2.
          rewrite bindSame, bindDiff, E1, bindSame.
            { apply H. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
        + assumption.
        + assumption.
        + assumption.
    - rewrite evalAll. intros y.
      remember (bind e n x) as e1 eqn:E1. remember (bind e1 m y) as e2 eqn:E2.
      rewrite evalIff, evalEqu, evalAll, E2, bindSame, bindDiff, E1, bindSame.
      destruct (H x y) as [H1 H2]. clear H. split; intros H'.
        + intros z. rewrite <- E1, <- E2, evalIff, evalElem, evalElem, bindSame.
          rewrite  bindDiff, bindDiff, E2, bindSame, bindDiff, E1, bindSame.
           apply H1.
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
        + apply H2. intros z. remember (H' z) as H eqn:E. clear E. clear H'.
          rewrite <- E1 in H. rewrite <- E2 in H. rewrite evalIff in H.
          rewrite evalElem in H. rewrite evalElem in H. rewrite bindSame in H.
          rewrite bindDiff in H. rewrite bindDiff in H. rewrite E2 in H.
          rewrite bindSame in H. rewrite bindDiff in H. rewrite E1 in H.
          rewrite bindSame in H.
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
            { assumption. }
        + assumption.
        + assumption.
        + assumption.
Qed.

Import SemanCtx.
Lemma evalExtensionalityFCtx : LEM -> forall (G:Context) (n m p:nat),
    n <> m  ->
    n <> p  ->
    m <> p  ->
    G :- (extensionalityF n m p) >>
        forall (x y:set), x == y <-> forall (z:set), z :: x <-> z :: y.
Proof.
    intros L G n m p H1 H2 H3. unfold extensionalityF.
    apply evalAll. intros x. apply evalAll. intros y.
    apply evalIff; try assumption.
    - apply evalEqu; try assumption.
        + apply FindS. assumption. apply FindZ.
        + apply FindZ.
    - apply evalAll. intros z. apply evalIff; try assumption.
        + apply evalElem; try (apply FindZ).
          apply FindS; try assumption. apply FindS; try assumption.
          apply FindZ.
        + apply evalElem; try (apply FindZ).
          apply FindS; try assumption. apply FindZ.
Qed.

Import Semantics.
(* Evaluating doubleInclF in any environment 'yields' the theorem doubleIncl.   *)
Lemma evalDoubleInclF : LEM -> forall (e:Env) (n m:nat),
    m <> n -> 
    eval e (doubleInclF n m)
        <->
    forall (x y:set), x == y <-> (x <= y) /\ (y <= x).
Proof.
    intros L e n m Hmn. unfold doubleInclF. rewrite evalAll. split; intros H x.
    - intros y. remember (H x) as H' eqn:E. clear E. clear H.
      rewrite evalAll in H'. remember (H' y) as H eqn:E. clear E. clear H'.
      remember (bind e n x) as e1 eqn:E1.
      rewrite evalIff in H. rewrite evalEqu in H. rewrite evalAnd  in H.
      rewrite evalSub in H. rewrite evalSub in H. rewrite bindSame in H. 
      rewrite bindDiff in H. rewrite E1 in H. rewrite bindSame in H.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
    - rewrite evalAll. intros y.
      remember (bind e n x) as e1 eqn:E1.
      rewrite evalIff, evalEqu, evalAnd, evalSub, evalSub, bindSame.
      rewrite bindDiff, E1, bindSame.
        + apply H.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
Qed.

