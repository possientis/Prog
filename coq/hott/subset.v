Require Import set.
Require Import equal.
Require Import belong.

Definition subset(x y:set) : Prop := forall (z:set), z % x -> z % y.

Notation "x <= y" := (subset x y) (at level 70, no associativity).


Lemma refl_incl : forall (a:set), a <= a.
Proof. intros x z H. assumption. Qed.

Lemma trans_incl : forall (a b c:set), a <= b -> b <= c -> a <= c.
Proof. intros a b c Hab Hbc x H. apply Hbc, Hab. assumption. Qed.

Definition subset'(x y:set) : Prop :=
    match x with
    | mkset a f     =>
        match y with
        | mkset b g     =>
            forall (z:a), exists (z':b), f z = g z'
        end
    end.

(*
Lemma subset_subset' : forall (x y:set), subset x y -> subset' x y.
Proof.
    intros [a f] [b g] H. simpl. unfold subset in H. intros z.
    assert ((f z) % (mkset b g)) as E.
        { apply H. apply Belong. }
    clear H. apply belong_crit. assumption.
Qed.

Lemma subset'_subset : forall (x y:set), subset' x y -> subset x y.
Proof.
    intros [a f] [b g] H z H'. unfold subset' in H.
    apply belong_crit in H'. destruct H' as [x H'].
    assert (exists y, f x = g y) as H1. { apply H. }
    clear H. destruct H1 as [y H]. rewrite H', H.
    constructor.
Qed.
     
Lemma subset_equal : forall (x y:set), x <= y -> y <= x -> x == y.
Proof.
    intros [a f] [b g] H1 H2. split.
    - apply (subset_subset' (mkset a f) (mkset b g)). assumption.
    - apply (subset_subset' (mkset b g) (mkset a f)). assumption.
Qed.

Lemma equal_subset : forall (x y:set), x == y -> x <= y.
Proof.
    intros [a f] [b g] H. apply subset'_subset. 
    destruct H as [H1 H2]. assumption.
Qed.
*)
