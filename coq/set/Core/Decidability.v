Require Import List.

Require Import Core.Set.
Require Import Core.Order.
Require Import Core.Core.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Filter.
Require Import Core.Extensionality.

Lemma set_eq_dec : forall (x y:set), {x = y} + {x <> y}.
Proof.
    intros xs. induction xs as [|x IH1 xs IH2]; intros ys.
    - destruct ys as [|y ys].
        + left. reflexivity.
        + right. intros H. inversion H.
    - destruct ys as [|y ys].
        + right. intros H. inversion H.
        + destruct (IH1 y) as [H1|H1].
            { subst. destruct (IH2 ys) as [H2|H2].
                { subst. left. reflexivity. }
                { right. intros H. inversion H. apply H2. assumption. }}
            { right. intros H. inversion H. apply H1. assumption. }
Qed.


Lemma incl_n_dec : forall (n:nat) (xs ys:set), 
    { incl_n n xs ys } + { ~ incl_n n xs ys }.
Proof.
    induction n as [|n IH].
    - intros xs ys. left. apply I.
    - intros xs ys. destruct xs as [|x xs].
        + left. apply I.
        + destruct (IH xs ys) as [H|H].
            { simpl. 
              remember (fun y => incl_n n x y /\ incl_n n y x) as p eqn:P.
              assert (Dec p) as q.
                { unfold Dec. intros y. 
                  destruct (IH x y) as [H1|H1]; destruct (IH y x) as [H2|H2].
                    { left. rewrite P. split; assumption. }
                    { right. rewrite P. intros [H3 H4]. apply H2. assumption. }
                    { right. rewrite P. intros [H3 H4]. apply H1. assumption. }
                    { right. rewrite P. intros [H3 H4]. apply H1. assumption. }}
                  destruct (in_pred_dec _ p q (toList ys)) as [H'|H'].
                        { left. split.
                            { assumption. }
                            { rewrite P in H'. assumption. }}
                        { right. intros [H1 H2]. apply H'. 
                          rewrite P. assumption. }}
            { simpl. right. intros [H1 H2]. apply H. assumption. }
Qed.


Lemma incl_dec : forall (x y:set), { x <== y } + { ~ (x <== y) }.
Proof.
    intros x y. unfold incl. apply incl_n_dec.
Qed.

Lemma elem_dec : forall (x y:set), { x :: y } + { ~ x :: y }.
Proof.
    intros x y. unfold elem. apply incl_dec.
Qed.

Lemma equal_dec : forall (x y:set), { x == y } + { ~ (x == y) }.
Proof.
    intros x y.  
    destruct (incl_dec x y) as [H1|H1]; destruct (incl_dec y x) as [H2|H2].
    - left. apply doubleIncl. split; assumption.
    - right. rewrite doubleIncl. intros [H3 H4]. apply H2. assumption.
    - right. rewrite doubleIncl. intros [H3 H4]. apply H1. assumption.
    - right. rewrite doubleIncl. intros [H3 H4]. apply H1. assumption.
Qed.

