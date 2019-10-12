Require Import Le.
Require Import List.
Require Import Plus.

Require Import set.
Require Import nat.
Require Import Order.
Require Import Exists.
Require Import ToList.


Fixpoint subset_n (n:nat) : set -> set -> Prop :=
    match n with
    | 0     => (fun _  _    => True)
    | S n   => (fun xs ys   =>
        match xs with
        | Nil               => True
        | Cons x xs         =>
            subset_n n xs ys  (* xs <= ys *) 
        /\  Exists            (* there is y in ys such that x '=' y *) 
            (fun y => subset_n n x y /\ subset_n n y x)
            ys
        end)
    end.
 
(* This is not the definition of equality, merely syntactic sugar               *)
Definition equal_n (n:nat) (x y:set) : Prop :=
    subset_n n y x /\ subset_n n x y.

(* Technichal lemma needed later                                                *)
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

Lemma subset_n_Nil : forall (x:set) (n:nat), subset_n n Nil x.
Proof. intros x n. destruct n as [|n]; apply I. Qed.

Lemma subset_n_Cons : forall (xs ys y:set) (n:nat),
    order xs <= n -> subset_n n xs ys -> subset_n n xs (Cons y ys).
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
            { apply ExistsT. assumption. }
Qed.

Lemma subset_n_refl : forall (x:set) (n:nat),
    order x <= n -> subset_n n x x.
Proof.
    intros x n. revert x. induction n as [|n IH]; intros x H.
    - apply I.
    - destruct x as [|x xs].
        + apply I.
        + split.
            { apply subset_n_Cons.
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
            { apply ExistsH. split.
                { apply IH.
                  simpl in H. apply le_S_n in H.
                  apply le_trans with (max (order x) (order xs)).
                    { apply n_le_max. }
                    { assumption. }
                }
                { apply IH.
                  simpl in H. apply le_S_n in H.
                  apply le_trans with (max (order x) (order xs)).
                    { apply n_le_max. }
                    { assumption. }
                }
            }
Qed.

(*
Lemma subset_n_trans : forall (x y z:set) (n:nat),
    order x + order y + order z <= n ->
    subset_n n x y -> subset_n n y z -> subset_n n x z.
Proof.
    intros x y z n. revert x y z. 
    induction n as [|n IH]; intros x y z H.
    - intros. apply I.
    - intros H1 H2. destruct x as [|x xs].
        + apply subset_n_Nil.
        + destruct H1 as [H1 H1']. split.
            { apply IH with y.
                { admit. }
                { assumption. }
                { apply subset_n_Sn.
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
