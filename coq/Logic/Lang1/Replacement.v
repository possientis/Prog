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


(*
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
    (*
    apply H9.
        + apply Substitution.
            { exact H1. }
            { remember (bind (bind (bind e n x) m y) m' y'; replace2 0 1 n m)  
              as e1 eqn:E1. remember (bind (bind e 0 x) 1 y) as e2 eqn:E2.
              apply (relevance e1 e2).
                { intros k H10. rewrite E1, E2. unfold comp, bind, replace2.
                  destruct (eqDec k 0) as [H11|H11] eqn:K0.
                    { subst. destruct (eqDec m' n) as [H12|H12].
                        { subst. exfalso. apply H4. reflexivity. }   
                        { destruct (eqDec m n) as [H13|H13].
                            { subst. exfalso. apply H3. reflexivity. } 
                            { simpl. destruct (PeanoNat.Nat.eq_dec n n) 
                              as [H14|H14].
                                { apply equalRefl. }
                                { exfalso. apply H14. reflexivity. }}}}
                    { destruct (eqDec k 1) as [H12|H12] eqn:K1.
                        { subst. destruct (eqDec m' m) as [H13|H13].
                            { subst. exfalso. apply H5. reflexivity. }
                            { simpl. destruct (PeanoNat.Nat.eq_dec m m) 
                              as [H14|H14].
                                { apply equalRefl. }
                                { exfalso. apply H14. reflexivity. }}}
                        { destruct (eqDec m' k) as [H13|H13].
                            { subst. exfalso. apply H5'. assumption. }
                            { destruct (eqDec m k) as [H14|H14].
                                { subst. exfalso. apply H4'. assumption. }
                                { destruct (eqDec n k) as [H15|H15].
                                    { subst. exfalso. apply H3'. assumption. }
                                    { destruct (eqDec 0 k) as [H16|H16];
                                      destruct (eqDec 1 k) as [H17|H17].
                                        { subst. inversion H17. }
                                        { exfalso. apply H11. symmetry.
                                          assumption. }
                                        { exfalso. apply H12. symmetry.
                                          assumption. }
                                        { apply equalRefl. }}}}}}} 
                { assumption. }}
        + apply Substitution.  
            { exact H2. }
            { remember (bind (bind (bind e n x) m y) m' y'; replace2 0 1 n m')  
              as e1 eqn:E1. remember (bind (bind e 0 x) 1 y') as e2 eqn:E2.
              apply (relevance e1 e2).
                { intros k H10. rewrite E1, E2. unfold comp, bind, replace2.
                  destruct (eqDec k 0) as [H11|H11] eqn:K0.
                    { subst. destruct (eqDec m' n) as [H12|H12].
                        { subst. exfalso. apply H4. reflexivity. }
                        { destruct (eqDec m n) as [H13|H13].
                            { subst. exfalso.  apply H3. reflexivity. }
                            { simpl. destruct (PeanoNat.Nat.eq_dec n n) 
                              as [H14|H14].
                                { apply equalRefl. }
                                { exfalso. apply H14. reflexivity. }}}}
                    { destruct (eqDec k 1) as [H12|H12] eqn:K1.
                        { subst. destruct (eqDec m' m') as [H13|H13].
                            { apply equalRefl. }
                            { exfalso. apply H13. reflexivity. }}
                        { destruct (eqDec m' k) as [H13|H13].
                            { subst. exfalso. apply H5'. assumption. }
                            { destruct (eqDec m k) as [H14|H14].
                                { subst. exfalso. apply H4'. assumption. }
                                { destruct (eqDec n k) as [H15|H15].
                                    { subst. exfalso. apply H3'. assumption. }
                                    { destruct (eqDec 0 k) as [H16|H16];
                                      destruct (eqDec 1 k) as [H17|H17].
                                        { subst. inversion H17. }
                                        { exfalso. apply H11. symmetry.
                                          assumption. }
                                        { exfalso. apply H12. symmetry.
                                          assumption. }
                                        { apply equalRefl. }}}}}}} 
                { assumption. }}
        + intros H10. apply H5. symmetry. assumption.
        + assumption.
    - rewrite evalAll. intros y. rewrite evalAll. intros y'. rewrite evalImp.
      rewrite evalImp, evalEqu, bindSame, bindDiff, bindSame.
*)
Show.
*)
