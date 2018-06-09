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

Lemma subset_subset' : forall (x y:set), subset x y -> subset' x y.
Proof.
    intros [a f] [b g] H. simpl. unfold subset in H. intros z.
    assert ((f z) % (mkset b g)) as E.
        { apply H. apply Belong. }
    clear H. apply belong_crit. assumption.
Qed.

(*
Lemma subset'_subset : forall (x y:set), subset' x y -> subset x y.
Proof.

Show.
*)
