Require Import List.

Require Import Core.Set.

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


Lemma filter_nil : forall (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a),
    (exists (x:a), In x xs /\ p x) <-> filter q xs <> nil.
Proof.
    intros a p q xs. induction xs as [|x xs IH]. 
    - split.
        + intros [x [H1 H2]]. inversion H1.
        + intros H. exfalso. apply H. reflexivity.
    - split.
        + intros [y [H1 H2]]. destruct (q x) as [H|H] eqn:E; simpl; rewrite E.
            { intros H'. inversion H'. }
            { apply IH. destruct H1 as [H1|H1].
                { subst. exfalso. apply H. assumption. }
                { exists y. split; assumption. }}
        + destruct (q x) as [H|H] eqn:E; simpl; rewrite E.
            { intros H'. exists x. split.
                { left. reflexivity. }
                { assumption. }}
            { intros H'. apply IH in H'. destruct H' as [y [H1 H2]].
              exists y. split.
                { right. assumption. }
                { assumption. }}
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

