Require Import Peano_dec.

Require Import Core.Set.
Require Import Core.Equal.
Require Import Core.Compatible.

Require Import Lang1.Syntax.
Require Import Lang1.Environment.
Require Import Lang1.Semantics.
Require Import Lang1.Relevance.


(* Any predicate obtained by a formula is a compatible predicate.               *)
Theorem formulaCompatible : forall (e:Env) (p:Formula) (n:nat),
    compatible (eval1 e p n). 
Proof.
    intros e p n. revert e n. induction p as [|k m|p1 IH1 p2 IH2|m p1 IH1];
    intros e n; unfold compatible, eval1; intros x y E; simpl; intros H.
    - assumption.
    - apply elemCompatL with (bind e n x k). 
        + apply bindEqual. assumption.
        + apply elemCompatR with (bind e n x m).
            { apply bindEqual. assumption. }
            { assumption. }
    - unfold compatible, eval1 in IH1. unfold compatible, eval1 in IH2. intros H'.
      apply IH2 with x.
        + assumption.
        + apply H. apply IH1 with y.
            { apply equalSym. assumption. }
            { assumption. }
    - intros z. unfold compatible, eval1 in IH1. 
      destruct (eq_nat_dec m n) as [H'|H'].
        + subst. apply (evalEnvEqual (bind (bind e n y) n z) (bind e n z)).
            { apply bindOver. }
            { apply (evalEnvEqual (bind (bind e n x) n z) (bind e n z)).
                { apply bindOver. }
                { apply H. }}
        + apply (evalEnvEqual 
            (bind (bind e n y) m z)
            (bind (bind e m z) n y)).
            { apply bindPermute. assumption. }
            { apply IH1 with x.
                { assumption. }
                { apply (evalEnvEqual 
                    (bind (bind e n x) m z)
                    (bind (bind e m z) n x)).
                    { apply bindPermute. assumption. }
                    { apply H. }}}
Qed.


(* Any two-fold predicate obtained by a formula is a compatible predicate.      *)
Theorem formulaCompatible2 : forall (e:Env) (p:Formula) (n m:nat),
    compatible2 (eval2 e p n m).
Proof.
    unfold eval2. intros e p n m x x' y y' Hx Hy H.
    remember (formulaCompatible (bind e n x') p m) as H' eqn:E. clear E.
    unfold compatible in H'. unfold eval1 in H'. apply H' with y; clear H'.
    - assumption.
    -  apply evalEnvEqual with (bind (bind e n x) m y).
        + apply bindEnvEqual.
            { apply bindEnvEqual.
                { apply envEqualRefl. }
                { apply equalSym. assumption. }} 
            { apply equalRefl. }
        + assumption.
Qed.

