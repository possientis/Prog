Require Import Peano_dec.

Require Import Utils.Ord.

Require Import Core.Set.
Require Import Core.Decidability.


(* Ordering of syntactic representations of sets. This relation is not          *)
(* compatible with set equality (==) and is used for normalization only.        *)
Fixpoint leq (x y:set) : Prop :=
    match x with
    | Nil           => True
    | (Cons x xs)   =>
        match y with
        | Nil           => False
        | (Cons y ys)   => (x <> y) /\ (leq x y)     (* lexicographic order     *)
                        \/ (x = y)  /\ (leq xs ys)
        end
    end.

(* Strict equality between sets is decidable so leq itself is decidable.        *)
Lemma leqDec : forall (x y:set), {leq x y} + {~leq x y}.
Proof.
    induction x as [|x IH1 xs IH2]; intros y.
    - left. apply I.
    - destruct y as [|y ys].
        + right. simpl. unfold not. intros. contradiction.
        + destruct (eqDecSet x y) as [H1|H1].
            { destruct (IH2 ys) as [H2|H2].
                { left. right. split; assumption. }
                { right. simpl. intros [[H3 H4]|[H3 H4]].
                    { apply H3 in H1. contradiction. }
                    { apply H2 in H4. contradiction. }}}
            { destruct (IH1 y) as [H2|H2].
                { left. left. split; assumption. }
                { right. simpl. intros [[H3 H4]|[H3 H4]].
                    { apply H2 in H4. contradiction. }
                    { apply H1 in H3. contradiction. }}}
Qed.

Lemma leqRefl : forall (x:set), leq x x.
Proof.
    induction x as [|x _ xs IH].
    - apply I.
    - right. split.
        + reflexivity.
        + apply IH.
Qed.

Lemma leqxNil : forall (x:set), leq x Nil -> x = Nil.
Proof.
    intros x. destruct x as [|x xs]. 
    - intros. reflexivity.
    - simpl. intros. contradiction.
Qed.

Lemma leqASym : forall (x y:set), leq x y -> leq y x -> x = y.
Proof.
    induction x as [|x IH1 xs IH2].
    - intros y H1 H2. symmetry. apply leqxNil. assumption.
    - intros [|y ys].
        + intros H. apply leqxNil in H. inversion H.
        + simpl. intros [[H1 H2]|[H1 H2]].
            { intros [[H3 H4]|[H3 H4]].
                { exfalso. apply H1. apply IH1; assumption. }
                { exfalso. apply H1. symmetry. assumption. }}
            { intros [[H3 H4]|[H3 H4]].
                { exfalso. apply H3. symmetry. assumption. }
                { subst. rewrite (IH2 ys).
                    { reflexivity. }
                    { assumption. }
                    { assumption. }}}
Qed.


Lemma leqTrans : forall (x y z:set), leq x y -> leq y z -> leq x z. 
Proof.
    induction x as [|x IH1 xs IH2]; intros y z H1 H2.
    - apply I.
    - destruct z as [|z zs].
        + apply leqxNil in H2. subst. apply leqxNil in H1. inversion H1.
        + simpl. destruct (eqDecSet x z) as [H|H].
            { subst. right. split.
                { reflexivity. }
                { destruct y as [|y ys]. 
                    { apply leqxNil in H1. inversion H1. }
                    { simpl in H1. simpl in H2. 
                        destruct H1 as [[H1 H3]|[H1 H3]].
                            { destruct H2 as [[H2 H4]|[H2 H4]].
                                { exfalso. apply H1. apply leqASym; assumption. }
                                { exfalso. apply H1. symmetry. assumption. }}    
                            { destruct H2 as [[H2 H4]|[H2 H4]].
                                { exfalso. apply H2. symmetry. assumption. }
                                { subst. apply IH2 with ys; assumption. }}}}}
            { left. split.
                { assumption. }
                { destruct y as [|y ys].
                    { apply leqxNil in H1. inversion H1. }
                    { simpl in H1. simpl in H2. 
                        destruct H1 as [[H1 H3]|[H1 H3]].
                            { destruct H2 as [[H2 H4]|[H2 H4]].
                                { apply IH1 with y; assumption. }
                                { subst. assumption. }}
                            { destruct H2 as [[H2 H4]|[H2 H4]].
                                { subst. assumption. }
                                { subst. apply leqRefl. }}}}}
Qed.                            


Lemma leqTotal : forall (x y:set), leq x y \/ leq y x.
Proof.
    induction x as [|x IH1 xs IH2]; intros y.
    - left. apply I. 
    - destruct y as [|y ys].
        + right. apply I.
        + destruct (eqDecSet x y) as [H|H].
            { subst. destruct (IH2 ys) as [H|H].
                { left. right. split.
                    { reflexivity. }
                    { assumption. }}
                { right. right. split.
                    { reflexivity. }
                    { assumption. }}}
            { destruct (IH1 y) as [H'|H'].
                { left. left. split; assumption. }
                { right. left. split.
                    { intros E. apply H. symmetry. assumption. }
                    { assumption. }}}
Qed.

Instance ordSet : Ord set :=
    { leq      := leq
    ; leqDec   := leqDec
    ; leqRefl  := leqRefl
    ; leqTrans := leqTrans
    ; leqAsym  := leqASym
    ; leqTotal := leqTotal
    }. 
