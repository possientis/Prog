Require Import List.

Require Import Core.Set.
Require Import Core.Order.
Require Import Core.Core.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
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

Definition Dec (a:Type) (p:a -> Prop) := forall (x:a), {p x} + {~p x}.

Arguments Dec {a}.

Fixpoint filter (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a) : list a :=
    match xs with
    | nil       => nil
    | cons x xs => 
        match q x with
        | left  _   => cons x (filter a p q xs)
        | right _   => filter a p q xs
        end
    end.

Arguments filter {a} {p}.

Lemma filter_equiv : forall (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a) (x:a),
    In x xs /\ p x <-> In x (filter q xs).
Proof.
    intros a p q xs x. induction xs as [|y xs IH].
    - simpl. split.
        + intros [H1 H2]. assumption.
        + intros H. exfalso. assumption.
    - split.
        + intros [[H1|H1] H2].
            { subst. destruct (q x) as [H|H] eqn:E.
                {simpl. rewrite E. left. reflexivity. }
                {exfalso. apply H. assumption. }}
            { destruct (q y) as [H|H] eqn:E; simpl; rewrite E.
                { right. apply IH. split; assumption. }
                { apply IH. split; assumption. }}
        + destruct (q y) as [H|H] eqn:E; simpl; rewrite E.
            { intros [H'|H'].
                { split; subst.
                    { left. reflexivity. }
                    { assumption. }}
                { apply IH in H'. destruct H' as [H1 H2]. split.
                    { right. assumption. }
                    { assumption. }}}
            { intros H'. apply IH in H'. destruct H' as [H1 H2]. split.
                    { right. assumption. }
                    { assumption. }}
Qed.

Lemma exists_nil : forall (a:Type) (xs:list a),
    (exists (x:a), In x xs) <-> xs <> nil.
Proof.
    intros a xs. destruct xs as [|x xs]; split.
    - intros [x H]. inversion H.
    - intros H. exfalso. apply H. reflexivity.
    - intros H1 H2. inversion H2.
    - intros H. exists x. left. reflexivity.
Qed.

Lemma filter_nil : forall (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a),
    (exists (x:a), In x xs /\ p x) <-> filter q xs <> nil.
Proof.
    intros a p q xs. split.
    - intros [x H]. apply exists_nil. exists x. apply filter_equiv. assumption.
    - intros H. apply exists_nil in H. destruct H as [x H]. exists x.
      apply (filter_equiv a p q). assumption.
Qed.

Arguments filter_nil {a} {p}.

Lemma nil_dec : forall (a:Type) (xs:list a), {xs = nil} + {xs <> nil}.
Proof.
    intros a xs. destruct xs as [|x xs].
    - left. reflexivity.
    - right. intros H. inversion H.
Qed.


Arguments nil_dec {a}.


Theorem in_pred_dec : forall (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a),
    {exists (x:a), In x xs /\ p x} + {~ exists (x:a), In x xs /\ p x}.
Proof.
    intros a p q xs. destruct (nil_dec (filter q xs)) as [H|H] eqn:E.
    - right. intros H'. apply (filter_nil q) in H'. apply H'. assumption.
    - left. apply (filter_nil q). assumption.
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

