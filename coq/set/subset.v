Require Import Arith.Le.
Require Import Arith.Plus.

Require Import set.
Require Import nat.
Require Import Order.
Require Import Subset_n.

Definition subset (xs ys:set) : Prop :=
    let n := order xs + order ys in subset_n n xs ys.

Lemma subset_charac : forall (xs ys:set), subset xs ys <-> 
    forall (n:nat), order xs + order ys <= n -> subset_n n xs ys.
Proof.
    intros xs ys. unfold subset. split; intros H.
    - intros n H'.
      remember (order xs + order ys) as m eqn:E. revert E.
      induction H' as [|n H1 IH]; intros H2.
        + assumption.
        + apply (subset_n_Sn n).
            { rewrite <- H2. assumption. }
            { apply IH. assumption. }
    - apply H. apply le_n.
Qed.

Notation "x <== y" := (subset x y) (at level 90) : set_scope.

Open Scope set_scope.

Lemma subset_Nil : forall (x:set), Nil <== x.
Proof.
    intros x. apply subset_charac. intros n H. apply subset_n_Nil.
Qed.

Lemma subset_Cons : forall (xs ys y:set), xs <== ys -> xs <== (Cons y ys).
Proof.
    intros xs ys y H. apply subset_charac. intros n H'. apply subset_n_Cons.
    - apply le_trans with (order xs + order (Cons y ys)). 
        + apply le_plus_l.
        + assumption.
    - apply subset_charac.
        + assumption.
        + apply weaken_r with (order (Cons y ys)).
            { assumption. }
            { simpl. apply le_S. apply m_le_max. }
Qed.

Lemma subset_refl : forall (x:set), x <== x.
Proof.
    intros x. apply subset_charac. intros n H.
    apply subset_n_refl. apply le_trans with (order x + order x).
    - apply le_plus_l.
    - assumption.
Qed.



