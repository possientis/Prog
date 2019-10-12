Require Import Le.
Require Import Plus.

Require Import Core.Set.
Require Import Core.Nat.
Require Import Core.Core.
Require Import Core.Order.

Definition incl (xs ys:set) : Prop :=
    let n := order xs + order ys in incl_n n xs ys.

Lemma incl_charac : forall (xs ys:set), incl xs ys <-> 
    forall (n:nat), order xs + order ys <= n -> incl_n n xs ys.
Proof.
    intros xs ys. unfold incl. split; intros H.
    - intros n H'.
      remember (order xs + order ys) as m eqn:E. revert E.
      induction H' as [|n H1 IH]; intros H2.
        + assumption.
        + apply (incl_n_Sn n).
            { rewrite <- H2. assumption. }
            { apply IH. assumption. }
    - apply H. apply le_n.
Qed.

Notation "x <== y" := (incl x y) (at level 90) : set_scope.

Open Scope set_scope.

Lemma incl_Nil : forall (x:set), Nil <== x.
Proof.
    intros x. apply incl_charac. intros n H. apply incl_n_Nil.
Qed.

Lemma incl_Cons : forall (xs ys y:set), xs <== ys -> xs <== (Cons y ys).
Proof.
    intros xs ys y H. apply incl_charac. intros n H'. apply incl_n_Cons.
    - apply le_trans with (order xs + order (Cons y ys)). 
        + apply le_plus_l.
        + assumption.
    - apply incl_charac.
        + assumption.
        + apply weaken_r with (order (Cons y ys)).
            { assumption. }
            { simpl. apply le_S. apply m_le_max. }
Qed.

Lemma incl_refl : forall (x:set), x <== x.
Proof.
    intros x. apply incl_charac. intros n H.
    apply incl_n_refl. apply le_trans with (order x + order x).
    - apply le_plus_l.
    - assumption.
Qed.



