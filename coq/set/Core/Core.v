Require Import Le.
Require Import List.
Require Import Plus.

Require Import Core.Set.
Require Import Core.Nat.
Require Import Core.Order.
Require Import Core.ToList.

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
                                    { apply toList_order. assumption. }
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
                                    { apply toList_order. assumption. }
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
                                    { apply toList_order. assumption. }
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
                                    { apply toList_order. assumption. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                    }
                }
            }
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

(*
Lemma incl_n_trans : forall (x y z:set) (n:nat),
    order x + order y + order z <= n ->
    incl_n n x y -> incl_n n y z -> incl_n n x z.
Proof.
    intros x y z n. revert x y z. 
    induction n as [|n IH]; intros x y z H.
    - intros. apply I.
    - intros H1 H2. destruct x as [|x xs].
        + apply incl_n_Nil.
        + destruct H1 as [H1 H1']. split.
            { apply IH with y.
                { admit. }
                { assumption. }
                { apply incl_n_Sn.
                    { admit. }
                    { assumption. }
                }
            }
            { destruct H1' as [y ys [p p'] |y ys H1'].
                { destruct H2 as [H2 H2']. 
                  destruct H2' as [z zs [q q']| z zs H2'].
                    { apply ExistsH. split.
                        { apply IH with y.
                            { admit. }
                            { assumption. }
                            { assumption. }
                        }
                        { apply IH with y.
                            { admit. }
                            { assumption. }
                            { assumption. }
                        }
                    }
                    { apply ExistsT. apply Exists_toList.
                      apply Exists_toList in H2'.
                      destruct H2' as [u [H3 [H4 H5]]].
                      exists u. split.
                        { assumption. }
                        { split.
                            { apply IH with y.
                                { admit. }
                                { assumption. }
                                { assumption. }
                            }
                            { apply IH with y.
                                { admit. }
                                { assumption. }
                                { assumption. }
                            }
                        }
                    }
                }
                { destruct H2 as [H2 H2']. 
                  destruct H2' as [z zs [q q']| z zs H2'].
                    { apply ExistsH.

Show.
*)
