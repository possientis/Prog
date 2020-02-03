Require Import Peano_dec.

Fixpoint fresh (n m:nat) : nat :=
    match eq_nat_dec 0 n, eq_nat_dec 0 m with
    | right _, right _  => 0 
    | left  _, left  _  => 1
    | left  _, right _  =>          (* n = 0 so cannot use 0 *)
        match eq_nat_dec 1 m with
        | left  _       => 2        (* m = 1 so cannot use 1 *)
        | right _       => 1 
        end
    | right _, left  _  =>          (* m = 0 so cannot use 0 *) 
        match eq_nat_dec 1 n with
        | left  _       => 2        (* n = 1 so cannot use 1 *)
        | right _       => 1      
        end
    end.

Lemma freshNot_n : forall (n m:nat), fresh n m <> n.
Proof.
    intros n m. unfold fresh. destruct n as [|n].
    - destruct (eq_nat_dec 0 0) as [H|H].
        + destruct (eq_nat_dec 0 m) as [H'|H'].
            { intros C. inversion C. }
            { destruct (eq_nat_dec 1 m) as [H0|H0].
                {intros C. inversion C. }
                {intros C. inversion C. }}
        + exfalso. apply H. reflexivity.
    - destruct (eq_nat_dec 0 (S n)) as [H|H].
        + inversion H.
        + destruct (eq_nat_dec 0 m) as [H'|H'].
            { destruct (eq_nat_dec 1 (S n)) as [H0|H0].
                { intros H1. rewrite <- H1 in H0. inversion H0. }
                { assumption. }}
            { assumption. }
Qed.

Lemma freshNot_m : forall (n m:nat), fresh n m <> m.
Proof.
    intros n m. unfold fresh. destruct n as [|n].
    - destruct (eq_nat_dec 0 0) as [H|H].
        + destruct (eq_nat_dec 0 m) as [H'|H'].
            { intros H0. rewrite <- H0 in H'. inversion H'. }
            { destruct (eq_nat_dec 1 m) as [H0|H0].
                { intros H1. rewrite <- H1 in H0. inversion H0. }
                { assumption. }}
        + destruct (eq_nat_dec 0 m) as [H'|H'].
            { exfalso. apply H. reflexivity. }
            { assumption. }
    - destruct (eq_nat_dec 0 (S n)) as [H|H].
        + destruct (eq_nat_dec 0 m) as [H'|H'].
            { intros H0. rewrite <- H0 in H'. inversion H'. }
            { destruct (eq_nat_dec 1 m) as [H0|H0].
                { intros H1. rewrite <- H1 in H0. inversion H0. }
                { assumption. }}
        + destruct (eq_nat_dec 0 m) as [H'|H'].
            { destruct (eq_nat_dec 1 (S n)) as [H0|H0].
                { intros H2. rewrite <- H2 in H'. inversion H'. }
                { intros H1. rewrite <- H1 in H'. inversion H'. }}
            { assumption. }
Qed.


Lemma checkFresh00 : fresh 0 0 = 1.
Proof. reflexivity. Qed.

Lemma checkFresh01 : fresh 0 1 = 2.
Proof. reflexivity. Qed.

Lemma checkFresh02 : fresh 0 2 = 1.
Proof. reflexivity. Qed.

Lemma checkFresh10 : fresh 1 0 = 2.
Proof. reflexivity. Qed.

Lemma checkFresh11 : fresh 1 1 = 0.
Proof. reflexivity. Qed.

Lemma checkFresh12 : fresh 1 2 = 0.
Proof. reflexivity. Qed.

Lemma checkFresh22 : fresh 2 2 = 0.
Proof. reflexivity. Qed.
