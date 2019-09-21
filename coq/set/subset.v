Require Import Arith.Plus.
Require Import Arith.PeanoNat.

Require Import set.
Require Import nat.
Require Import Exists.
Require Import Order.
 
(* This is based on the wrong notion of equality, but it may be fine in the end *)
Fixpoint subset_n (n:nat) : set -> set -> Prop :=
    match n with
    | 0     => (fun _  _    => True)
    | S n   => (fun xs ys   =>
        match xs with
        | Nil               => True
        | Cons x xs         =>
            subset_n n xs ys  (* xs <= ys *) 
        /\  Exists            (* there is y in ys such that x = y *) 
            (fun y => subset_n n x y /\ subset_n n y x)
            ys
        end)
    end.
              
(* This is the wrong definition of equality, but it may be fine in the end      *)
Definition equal_n (n:nat) (x:set) (y:set) : Prop :=
    subset_n n y x /\ subset_n n x y.

Lemma exists_equal_ind : forall (n m:nat) (xs ys:set), 
    (forall (xs ys:set), order xs + order ys <= n -> 
        (subset_n n xs ys) <-> (subset_n m xs ys))      ->
order xs + order ys <= n                                ->
Exists (fun (y:set) => equal_n n y xs) ys               <->
Exists (fun (y:set) => equal_n m y xs) ys.
Proof.
    intros n m xs ys H H'. split; intros I; revert H'.
    - induction I as [x ys [H1 H2]|x ys H1 IH]; intros H'.
        + apply ExistsH. unfold equal_n. split.
            { apply H. 
                { apply weaken_r with (order (Cons x ys)).
                    { assumption. }
                    { simpl. apply le_S. apply n_le_max.
                    }
                }
                { assumption. }
            }
            { apply H.
                { rewrite plus_comm. apply weaken_r with (order (Cons x ys)).
                    { assumption. }
                    { simpl. apply le_S. apply n_le_max. }
                }
                { assumption. }
            }
        + apply ExistsT. apply IH. apply weaken_r with (order (Cons x ys)).
            { assumption. }
            { simpl. apply le_S. apply m_le_max. }
    - induction I as [x ys [H1 H2]|x ys H1 IH]; intros H'.
        + apply ExistsH. unfold equal_n. split.
            { apply H.
                { apply weaken_r with (order (Cons x ys)).
                    { assumption. }
                    { simpl. apply le_S. apply n_le_max. }
                }
                { assumption. }
            }
            { apply H.
                { rewrite plus_comm. apply weaken_r with (order (Cons x ys)).
                    { assumption. }
                    { simpl. apply le_S. apply n_le_max. }
                }
                { assumption. }
            }
        + apply ExistsT. apply IH. apply weaken_r with (order (Cons x ys)).
            { assumption. }
            { simpl. apply le_S. apply m_le_max. }
Qed.



Lemma subset_n_Sn : forall (n:nat) (xs ys:set),
    order xs + order ys <= n -> (subset_n n xs ys <-> subset_n (S n) xs ys).
Proof.
    induction n as [|n IH]; intros xs ys.
    - intros H. apply le_0 in H. apply sum_0 in H. destruct H as [H1 H2].
      apply order_0 in H1. apply order_0 in H2. rewrite H1, H2. simpl.
      split; intros H; assumption.
    - intros H. split.
        + intros H'. destruct xs as [|x xs].
            { apply I. }
            { remember (S n) as m eqn:E.
              rewrite E in H'. simpl in H'. destruct H' as [H1 H2].
              simpl. split.
                { apply IH.
                    { apply weaken_l' with (order (Cons x xs)).
                        { rewrite E in H. assumption. }
                        { simpl. apply le_n_S. rewrite max_sym. apply n_le_max. }
                    }
                    { assumption. } 
                }
                { destruct H2 as [y ys [H2 H3]|y ys H2].
                    { apply ExistsH. split.
                        { apply IH.
                            { apply weaken_l' with (order (Cons x xs)).
                                {  apply weaken_r with (order (Cons y ys)).
                                    { rewrite E in H. assumption. }
                                    { simpl. apply le_S. apply n_le_max. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                        { apply IH.
                            { rewrite plus_comm. 
                              apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order (Cons y ys)).
                                    { rewrite E in H. assumption. }
                                    { simpl. apply le_S. apply n_le_max. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                    }
                    { apply ExistsT. apply (exists_equal_ind n m x ys).
                        { assumption. }
                        { apply weaken_l' with (order (Cons x xs)).
                            { apply weaken_r with (order (Cons y ys)).
                                { rewrite E in H. assumption. }
                                { simpl. apply le_S. apply m_le_max. }
                            }
                            { simpl. apply le_n_S. apply n_le_max. }
                        }
                        { assumption. }
                    }
                }
            }
        + intros H'. destruct xs as [|x xs].
            { apply I. }
            { remember (S n) as m eqn:E. destruct H' as [H1 H2].
              rewrite E. split.
                { apply IH.
                    { apply weaken_l' with (order (Cons x xs)).
                        { rewrite E in H. assumption. }
                        { simpl. apply le_n_S. apply m_le_max. }
                    }
                    { assumption. }
                }
                { destruct H2 as [y ys [H2 H3]|y ys H2].
                    { apply ExistsH. split.
                        { apply IH.
                            { apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order (Cons y ys)).
                                    { rewrite E in H. assumption. }
                                    { simpl. apply le_S. apply n_le_max. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                        { apply IH.
                            { rewrite plus_comm. 
                              apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order (Cons y ys)).
                                    { rewrite E in H. assumption. }
                                    { simpl. apply le_S. apply n_le_max. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption . }
                        }
                    }
                    { apply ExistsT.  apply (exists_equal_ind n m x ys).                   
                        { assumption. }
                        { apply weaken_l' with (order (Cons x xs)).
                            { apply weaken_r with (order (Cons y ys)).
                                { rewrite E in H. assumption. }
                                { simpl. apply le_S. apply m_le_max. }
                            }
                            { simpl. apply le_n_S. apply n_le_max. }
                        }
                        { assumption. }
                    }
                }
            } 
Qed.

Definition subset (xs ys:set) : Prop :=
    let n := order xs + order ys in subset_n n xs ys.

Lemma subset_charac : forall (n:nat) (xs ys:set),
    order xs + order ys <= n -> (subset xs ys <-> subset_n n xs ys).
Proof.
    intros n xs ys H. remember (order xs + order ys) as m eqn:E. revert E. 
    induction H as [|n H IH].
    - intros H. unfold subset. rewrite <- H. split; intros H'; assumption.
    - intros H1. split; intros H2.
        + apply (subset_n_Sn n).
            { rewrite <- H1. assumption. }
            { apply IH; assumption. }
        + apply IH.
            { assumption. }
            { apply subset_n_Sn. 
                { rewrite <- H1. assumption. }
                { assumption. }
            }
Qed.

Notation "x <== y" := (subset x y) (at level 90) : set_scope.


