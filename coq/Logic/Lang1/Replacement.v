Require Import List.

Require Import Logic.Class.Eq.
Require Import Logic.Axiom.LEM.

Require Import Logic.Func.Replace.
Require Import Logic.Func.Composition.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Syntax.
Require Import Logic.Fol.Functor.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Equal.
Require Import Logic.Set.Functional.
Require Import Logic.Set.Compatible.

Require Import Logic.Lang1.Apply.
Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Relevance.
Require Import Logic.Lang1.Environment.
Require Import Logic.Lang1.Substitution.

(* A n (A m (A m' (P n m -> P n m' -> m = m')))                                 *)
Definition functionalF (P:Formula) (n m m':nat) : Formula :=
    All n (All m (All m' (Imp (apply2 P n m) (Imp (apply2 P n m') (Equ m m'))))). 

Lemma evalFunctionalF : LEM -> forall (e:Env) (P:Formula) (n m m':nat),
    valid (replace2 0 1 n m)  P ->
    valid (replace2 0 1 n m') P ->
    n <> m  ->
    n <> m' ->
    m <> m' ->
    ~In n  (Fr P) ->
    ~In m  (Fr P) ->
    ~In m' (Fr P) ->
    eval e (functionalF P n m m')
        <->
    functional (eval2 e P 0 1).
Proof.
    intros L e P n m m' H1 H2 H3 H4 H5 H3' H4' H5'. 
    unfold functional, functionalF, eval2. rewrite evalAll.
    split; intros H6 x.
    - intros y y' H7 H8. 
      remember (H6 x)  as H9 eqn:E. clear E H6. rewrite evalAll in H9.
      remember (H9 y)  as H6 eqn:E. clear E H9. rewrite evalAll in H6.
      remember (H6 y') as H9 eqn:E. clear E H6. rewrite evalImp in H9.
      rewrite evalImp in H9. rewrite evalEqu in H9.
      rewrite bindDiff in H9. rewrite bindSame in H9. rewrite bindSame in H9.
      apply H9.
        + apply evalApplyF1; assumption. 
        + apply evalApplyF2; assumption.
        + auto.
        + assumption.
    - rewrite evalAll. intros y. rewrite evalAll. intros y'. 
      rewrite evalImp, evalImp, evalEqu, bindDiff, bindSame, bindSame.
      intros H7 H8. apply H6 with x.
        + rewrite <- evalApplyF1; try (exact H7); assumption.
        + rewrite <- evalApplyF2; try (exact H8); assumption.
        + auto.
        + assumption.
Qed.

Definition replacementF (P:Formula) (q r r' n m k l:nat) : Formula :=
    All n (Imp 
        (functionalF P q r r')
        (Exi m (All k (Iff 
            (Elem k m) 
            (Exi l (And (Elem l n) (apply2 P l k))))))). 

(* Very inelegant. Many conditions need to be met for the (replacementF P)      *)
(* statement to have the right semantics. Part of the problem is the language   *)
(* in which the replacement axiom schema is expressed, which has no lambda      *)
(* abstraction and function application which would allow us to nicely express  *)
(* the fact that P is a predicate of two variables and P x y holds.             *)
Lemma evalReplacementF : LEM -> forall (e:Env) (P:Formula) (q r r' n m k l:nat),
    q <> r  ->
    q <> r' ->
    r <> r' ->
    m <> n  ->
    k <> n  ->
    l <> n  ->
    k <> m  -> 
    m <> l  ->
    l <> k  ->
    0 <> m  ->
    1 <> m  ->
    ~In q  (Fr P) ->
    ~In r  (Fr P) ->
    ~In r' (Fr P) ->
    ~In k  (Fr P) ->
    ~In l  (Fr P) -> 
    ~In m  (Fr P) ->
    valid (replace2 0 1 q r ) P ->
    valid (replace2 0 1 q r') P ->
    valid (replace2 0 1 l k ) P ->
    eval e (replacementF P q r r' n m k l)
        <->
    forall (x:set),
        functional (eval3 e P n 0 1 x) ->
            exists (y:set), forall (z:set),
                z :: y <-> exists (u:set), u :: x /\ (eval3 e P n 0 1 x u z).
Proof.
    intros 
        L e P q r r' n m k l 
        H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11
        H1' H2' H3' H4' H5' H6'
        V1 V2 V3.
    split; intros G1.
    - intros x G2. unfold replacementF in G1. rewrite evalAll in G1.
      remember (G1 x) as G3 eqn:E. clear E G1. rename G3 into G1. 
      rewrite evalImp in G1. unfold eval3 in G2. 
      fold (eval2 (bind e n x) P 0 1) in G2.
      rewrite <- (evalFunctionalF L (bind e n x) P q r r') in G2; 
      try assumption. remember (G1 G2) as G3 eqn:E. clear G1 E G2. 
      rewrite evalExi in G3; try assumption. destruct G3 as [y G1]. 
      exists y. intros z. 
      rewrite evalAll in G1. remember (G1 z) as G2 eqn:E. clear E G1.
      rewrite evalIff in G2; try assumption.
      rewrite evalElem in G2. rewrite bindSame in G2.
      rewrite bindDiff in G2; try assumption. rewrite bindSame in G2.
      rewrite evalExi in G2; try assumption. 
      destruct G2 as [G1 G2]. split; intros G3.
        + apply G1 in G3. clear G1 G2. destruct G3 as [u G1]. exists u.
          rewrite evalAnd in G1; try assumption.
          rewrite evalElem in G1. rewrite bindSame in G1.
          rewrite bindDiff in G1; try assumption.
          rewrite bindDiff in G1; try assumption.
          rewrite bindDiff in G1; try assumption. 
          rewrite bindSame in G1. destruct G1 as [G2 G1].
          split; try assumption. clear G2.
          remember (bind (bind (bind (bind e n x) m y) k z) l u) as e1 eqn:E1.
          remember (bind (bind (bind (bind e n x) m y) l u) k z) as e2 eqn:E2.
          rewrite (evalEnvEqual e1 e2) in G1.
            { rewrite E2 in G1. remember (bind (bind e n x) m y) as e' eqn:E'.
              rewrite (evalApply2 e' P l k u z) in G1; try assumption.
              unfold eval3. unfold eval2 in G1. rewrite E' in G1.
              clear E1 e1 E2 e2 E' e'. remember 
              (bind (bind (bind (bind e n x) m y) 0 u) 1 z) as e1 eqn:E1.
              remember (bind (bind (bind e n x) 0 u) 1 z) as e2 eqn:E2.
              apply (relevance e1 e2).
                { remember (bind (bind (bind e n x) m y) 0 u) as e3 eqn:E3.
                  remember (bind (bind (bind e n x) 0 u) m y) as e4 eqn:E4.
                  assert (envEqual e3 e4) as G2.
                    { rewrite E3, E4. apply bindPermute. assumption. }
                  assert (envEqual e1 (bind e4 1 z)) as G3.
                    { rewrite E1. apply bindEnvEqual.
                        { assumption. }
                        { apply equalRefl. }}
                  rewrite E4 in G3. clear E4 G2 e4. 
                  remember 
                    (bind (bind (bind (bind e n x) 0 u) m y) 1 z) as e4 eqn:E4.
                  remember 
                    (bind (bind (bind (bind e n x) 0 u) 1 z) m y) as e5 eqn:E5.
                  assert (envEqual e4 e5) as G4.
                    { rewrite E4, E5. apply bindPermute. assumption. } 
                  rewrite E3 in E1. clear E3 e3. assert (envEqual e1 e5) as G5.
                    { apply envEqualTrans with e4; assumption. }
                  clear G4 G3 E4 e4. apply envEqualOnTrans with e5.
                    { apply envEqualEnvEqualOn. assumption. }
                    { clear E1 G1 G5 e1. rewrite E2, E5. apply bindNotInFree.
                      assumption. }}
                { assumption. }}
            { rewrite E1, E2. apply bindPermute. assumption. }
        + apply G2. clear G1 G2. destruct G3 as [u [G1 G2]]. exists u.
          rewrite evalAnd; try assumption.
          rewrite evalElem. rewrite bindSame. rewrite bindDiff; try assumption.
          rewrite bindDiff; try assumption. rewrite bindDiff; try assumption.
          rewrite bindSame. split; try assumption. rewrite eval3ToEval2 in G2.
          remember (bind (bind (bind (bind e n x) m y) k z) l u) as e1 eqn:E1.
          remember (bind (bind (bind (bind e n x) m y) l u) k z) as e2 eqn:E2.
          assert (envEqual e1 e2) as G3.
            { rewrite E1, E2. apply bindPermute. assumption. }
          apply evalEnvEqual with e2.
              { assumption. }
              { rewrite E2. clear G3 E1 E2 e1 e2. apply evalApply2; 
                try assumption. unfold eval2 in G2. unfold eval2.
                apply relevance with (bind (bind (bind e n x) 0 u) 1 z);
                try assumption. 
                apply bindEnvEqualOn; try (apply equalRefl).
                apply bindEnvEqualOn; try (apply equalRefl).
                apply bindNotInFree. assumption. }
    - unfold replacementF. rewrite evalAll. intros x. rewrite evalImp.
      intros G2. apply evalFunctionalF in G2; try assumption.
      rewrite evalExi; try assumption. remember (G1 x) as G3 eqn:E. clear E G1.
      unfold eval2 in G2. unfold eval3 in G3. remember (G3 G2) as G1 eqn:E.
      clear E G2 G3. destruct G1 as [y G1]. exists y. rewrite evalAll. intros z.
      rewrite evalIff; try assumption. rewrite evalElem, evalExi; 
      try assumption. rewrite bindSame, bindDiff; try assumption.
      rewrite bindSame. destruct (G1 z) as [G2 G3]. clear G1. split.
        + intros G4. clear G3. destruct (G2 G4) as [u [G1 G3]]. clear G2.
          exists u. rewrite evalAnd; try assumption.
          rewrite evalElem, bindSame, bindDiff; try assumption.
          rewrite bindDiff; try assumption. rewrite bindDiff; try assumption.
          rewrite bindSame. split; try assumption.
          remember (bind (bind (bind (bind e n x) m y) k z) l u) as e1 eqn:E1.
          remember (bind (bind (bind (bind e n x) m y) l u) k z) as e2 eqn:E2.
          clear G1. assert (envEqual e1 e2) as G1.
            { rewrite E1, E2. apply bindPermute. assumption. }
          apply (evalEnvEqual e1 e2); try assumption.
          rewrite E2. clear G1 E1 E2 e1 e2.
          fold (eval2 (bind (bind e n x) m y) (apply2 P l k) l k u z).
          apply evalApply2; try assumption. unfold eval2.
          remember (bind (bind (bind e n x) 0 u) 1 z) as e1 eqn:E1.
          remember (bind (bind (bind (bind e n x) m y) 0 u) 1 z) as e2 eqn:E2.
          apply (relevance e1 e2); try assumption. rewrite E1, E2.
          clear G3 E1 E2 e1 e2. apply bindEnvEqualOn; try apply equalRefl.
          apply bindEnvEqualOn; try apply equalRefl.
          apply envEqualOnSym, bindNotInFree. assumption.
        + intros [u G4]. clear G2. apply G3. clear G3. exists u.
          rewrite evalAnd in G4; try assumption.
          rewrite evalElem in G4. rewrite bindSame in G4.
          rewrite bindDiff in G4; try assumption. 
          rewrite bindDiff in G4; try assumption.
          rewrite bindDiff in G4; try assumption. rewrite bindSame in G4.
          destruct G4 as [G1 G2]. split; try assumption.
          remember (bind (bind (bind (bind e n x) m y) k z) l u) as e1 eqn:E1.
          remember (bind (bind (bind (bind e n x) m y) l u) k z) as e2 eqn:E2.
          clear G1. assert (envEqual e1 e2) as G1.
            { rewrite E1, E2. apply bindPermute. assumption. }
          apply (relevance e1 e2) in G2.
              { rewrite E2 in G2. clear G1 E1 E2 e1 e2.
                fold (eval2 (bind (bind e n x) m y) (apply2 P l k) l k u z) in G2.
                apply evalApply2 in G2; try assumption. unfold eval2 in G2.
                remember (bind (bind (bind e n x) 0 u) 1 z) as e1 eqn:E1.
                remember (bind (bind (bind (bind e n x) m y) 0 u) 1 z) 
                as e2 eqn:E2. apply (relevance e1 e2).
                    { rewrite E1, E2. clear G2 E1 E2 e1 e2.
                      apply bindEnvEqualOn; try apply equalRefl.
                      apply bindEnvEqualOn; try apply equalRefl.
                      apply envEqualOnSym, bindNotInFree. assumption. }
                    { assumption. }}
              { apply envEqualEnvEqualOn. assumption. }
Qed.
