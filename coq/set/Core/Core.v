Require Import Le.
Require Import List.
Require Import Plus.
Require Import Compare_dec.

Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Order.

Fixpoint incl_n (n:nat) (xs ys:set) : Prop := 
    match n with 
    | 0     => True
    | S n   => 
        match xs with
        | Nil                   => True
        | Cons x xs             =>
            incl_n n xs ys    /\
            exists (y:set), 
                In y (toList ys) /\ incl_n n x y /\ incl_n n y x 
        end
    end
.

Lemma incl_n_Sn : forall (n:nat) (xs ys:set),
    order xs + order ys <= n -> (incl_n n xs ys <-> incl_n (S n) xs ys).
Proof.
    induction n as [|n IH]; intros xs ys.
    - intros H. apply le_0 in H. apply sum_0 in H. destruct H as [H1 H2].
      apply order_0 in H1. apply order_0 in H2. rewrite H1, H2. simpl.
      split; intros H; assumption.
    - intros H. remember (S n) as m eqn:E. split.
        + intros H'. destruct xs as [|x xs].
            { apply I. }
            { rewrite E in H'. simpl in H'.    
              destruct H' as [H1 [y [H2 [H3 H4]]]].
              simpl. split.
                { apply IH.
                    { apply weaken_l' with (order (Cons x xs)).
                        { rewrite E in H. assumption. }
                        { simpl. apply le_n_S. rewrite max_sym. apply n_le_max. }
                    }
                    { assumption. }
                }
                { exists y. split.
                    { assumption. }
                    { split.
                        { apply IH. 
                            { rewrite E in H.
                              apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order ys).
                                    { assumption. }
                                    { apply orderToList. assumption. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                        { apply IH.
                            { rewrite plus_comm. rewrite E in H.
                              apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order ys).
                                    { assumption. }
                                    { apply orderToList. assumption. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                    }
                }
            }
        + intros H'. destruct xs as [|x xs]; rewrite E.
            { apply I. } 
            { simpl in H'. destruct H' as [H1 [y [H2 [H3 H4]]]]. split.
                { apply IH. 
                    { apply weaken_l' with (order (Cons x xs)).
                        { rewrite E in H. assumption. }
                        { simpl. apply le_n_S. apply m_le_max. }
                    }
                    { assumption. }
                } 
                { exists y. split.
                    { assumption. }
                    { split.
                        { apply IH.
                            { rewrite E in H.
                              apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order ys).
                                    { assumption. }
                                    { apply orderToList. assumption. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                        { apply IH.
                            { rewrite plus_comm. rewrite E in H.
                              apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order ys).
                                    { assumption. }
                                    { apply orderToList. assumption. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                    }
                }
            }
Qed.


Lemma incl_le_n_m : forall (xs ys:set) (n m:nat),
    order xs + order ys <= n    -> 
    n <= m                      -> 
    incl_n n xs ys              -> 
    incl_n m xs ys.
Proof.
    intros xs ys n m H1 H2. induction  H2  as [H2|m H2 IH].
    - auto.
    - intros H. apply (incl_n_Sn m).
        + apply le_trans with n; assumption.
        + apply IH. assumption.
Qed.

Lemma incl_le_m_n : forall (xs ys:set) (n m:nat),
    order xs + order ys <= n    -> 
    n <= m                      ->
    incl_n m xs ys              ->
    incl_n n xs ys.
Proof.
    intros xs ys n m H1 H2. induction  H2  as [H2|m H2 IH].
    - auto.
    - intros H. apply IH. apply incl_n_Sn.
        + apply le_trans with n; assumption.
        + assumption.
Qed.

Lemma incl_n_m : forall (xs ys:set) (n m:nat),
    order xs + order ys <= n    ->
    order xs + order ys <= m    ->
    incl_n n xs ys              -> 
    incl_n m xs ys.
Proof.
    intros xs ys n m Hn Hm H. destruct (le_dec n m) as [H'|H'].
    - apply incl_le_n_m with n; assumption.
    - apply incl_le_m_n with n.
        + assumption.
        + apply not_le in H'. unfold gt in H'. unfold lt in H'.
          apply le_trans with (S m).
            { apply le_S, le_n. }
            { assumption. }
        + assumption.
Qed.


Lemma incl_n_Nil : forall (x:set) (n:nat), incl_n n Nil x.
Proof. intros x n. destruct n as [|n]; apply I. Qed.

Lemma incl_n_Cons : forall (xs ys y:set) (n:nat),
    order xs <= n -> incl_n n xs ys -> incl_n n xs (Cons y ys).
Proof.
    intros xs ys y n. revert xs ys y. 
    induction n as [|n IH]; intros xs ys y H1 H2. 
    - apply I.
    - destruct xs as [|x xs].
        + apply I.
        + destruct H2 as [H2 H3]. split.
            { apply IH.
                { simpl in H1. apply le_S_n in H1. 
                  apply le_trans with (max (order x) (order xs)).
                    { apply m_le_max. }
                    { assumption. }
                }
                { assumption. }
            }
            { destruct H3 as [z [H3 [H4 H5]]]. 
              exists z. split.
                { right. assumption. }
                { split; assumption. }
            }
Qed.


Lemma incl_n_refl : forall (x:set) (n:nat),
    order x <= n -> incl_n n x x.
Proof.
    intros x n. revert x. induction n as [|n IH]; intros x H.
    - apply I.
    - destruct x as [|x xs].
        + apply I.
        + split.
            { apply incl_n_Cons.
                { simpl in H. apply le_S_n in H.
                  apply le_trans with (max (order x) (order xs)).
                    { apply m_le_max. }
                    { assumption. }
                }
                { apply IH. 
                  simpl in H. apply le_S_n in H.
                  apply le_trans with (max (order x) (order xs)).
                    { apply m_le_max. }
                    { assumption. }
                }
            }
            { exists x. split.
                { left. reflexivity. }
                { simpl in H. apply le_S_n in H. split; apply IH;
                  apply le_trans with (max (order x) (order xs)).
                      { apply n_le_max. }
                      { assumption. }
                      { apply n_le_max. }
                      { assumption. }
                }
            }
Qed.


