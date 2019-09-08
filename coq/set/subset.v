Require Import set.
Require Import nat.
Require Import Exists.
Require Import Order.
 
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
              
Definition equal_n (n:nat) (x:set) (y:set) : Prop :=
    subset_n n y x /\ subset_n n x y.


(*
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
                    { simpl.
*)
(*
                { assumption. }
            }
            { apply H.
                { admit. }
                { assumption. }
            }
        + apply ExistsT. apply IH. admit.
    - induction I as [x ys [H1 H2]|x ys H1 IH]; intros H'.
        + apply ExistsH. unfold equal_n. split.
            { apply H.
                { admit. }
                { assumption. }
            }
            { apply H.
                { admit. }
                { assumption. }
            }
        + apply ExistsT. apply IH. admit.
*)

(*
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
                    { admit. }
                    { assumption. } 
                }
                { destruct H2 as [y ys [H2 H3]|y ys H2].
                    { apply ExistsH. split.
                        { apply IH.
                            { admit. }
                            { assumption. }
                        }
                        { apply IH.
                            { admit. }
                            { assumption. }
                        }
                    }
                    { apply ExistsT. apply (exists_equal_ind n m x ys).
                        { assumption. }
                        { admit. }
                        { assumption. }
                    }
                }
            }
        + intros H'. destruct xs as [|x xs].
            { apply I. }
            { remember (S n) as m eqn:E. destruct H' as [H1 H2].
              rewrite E. split.
                { apply IH.
                    { admit. }
                    { assumption. }
                }
                { destruct H2 as [y ys [H2 H3]|y ys H2].
                    { apply ExistsH. split.
                        { apply IH.
                            { admit. }
                            { assumption. }
                        }
                        { apply IH.
                            { admit. }
                            { assumption . }
                        }
                    }
                    { apply ExistsT.  apply (exists_equal_ind n m x ys).                   
                        { assumption. }
                        { admit. }
                        { assumption. }
Admitted.
*)
