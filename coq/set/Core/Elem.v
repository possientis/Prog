Require Import Le.
Require Import List.
Require Import Plus.


Require Import Core.Set.
Require Import Core.Nat.
Require Import Core.Incl.
Require Import Core.Core.
Require Import Core.Order.
Require Import Core.ToList.

Notation "{ x }" := (Cons x Nil) : set_scope.

Open Scope set_scope.

Definition elem (x y:set) : Prop := incl {x} y. 

Notation "x :: y" := (elem x y) : set_scope.

Lemma elem_toList : forall (x xs:set), x :: xs <-> 
    exists (y:set), In y (toList xs) /\ (x <== y) /\ (y <== x).
Proof.
    intros x xs. split.
    - intros H. unfold elem in H. unfold incl in H. simpl in H.
      destruct H as [_ [y [H1 [H2 H3]]]]. exists y. split.
        + assumption.
        + split.
            { apply incl_n_incl with (max (order x) 0 + order xs).
                { apply le_trans with (order x + order xs).
                    { apply plus_le_compat_l. apply toList_order. assumption. }
                    { apply plus_le_compat_r. apply n_le_max. }
                    
                }
                { assumption. }
            }
            { apply incl_n_incl with (max (order x) 0 + order xs).
                { rewrite plus_comm.
                  apply le_trans with (order x + order xs).
                    { apply plus_le_compat_l. apply toList_order. assumption. }
                    { apply plus_le_compat_r. apply n_le_max. }
                }
                { assumption. }
            }
    - intros [y [H1 [H2 H3]]]. unfold elem. 
      apply incl_n_incl with (order {x} + order xs).
        + apply le_n.
        + split.
            { apply incl_n_Nil. }
            { exists y. split.
                { assumption. }
                { split.
                    { apply incl_incl_n.
                        { apply le_trans with (order x + order xs).
                            { apply plus_le_compat_l. 
                              apply toList_order. assumption. 
                            }
                            { apply plus_le_compat_r. apply n_le_max. }
                        }
                        { assumption. }
                    } 
                    { apply incl_incl_n. 
                        { rewrite plus_comm.
                          apply le_trans with (order x + order xs).
                            { apply plus_le_compat_l. 
                              apply toList_order. assumption. 
                            }
                            { apply plus_le_compat_r. apply n_le_max. }
                        }
                        { assumption. }
                    }
                }
            }
Qed.

(*
Lemma elem_incl_toList : forall (xs ys:set), xs <== ys <->
    (forall (z:set), In z (toList xs) -> z :: ys).
Proof.
    intros xs. induction xs as [|x _ xs IH]. 
    - admit.
    - intros ys. split.
        + intros H1 z H2. unfold incl in H1. simpl in H1.
          destruct H1 as [H1 [y [H3 [H4 H5]]]].
          destruct H2 as [H2|H2].
            { subst. apply elem_toList. exists y. split.
                { assumption. }
                { split.
                    { apply incl_n_incl 
                      with (max (order z) (order xs) + (order ys)).
                          { admit. }
                          { assumption. }
                    }
                    { apply incl_n_incl 
                      with (max (order z) (order xs) + (order ys)).
                          { admit. }
                          { assumption. }
                    }
                }
            }
            { apply IH.
                { apply incl_n_incl 
                  with (max (order x) (order xs) + (order ys)).
                      { admit. }
                      { assumption. }
                }
                { assumption. }
            }

        + intros H. unfold incl. simpl. split.
            { apply incl_incl_n.
                { admit. }
                { apply IH. intros z H'. apply H. right. assumption. }
            }
            {

Show.
*)

(*
Lemma elem_incl : forall (x y:set), 
    x <== y <-> forall (z:set), z :: x -> z :: y.
Proof.
    intros x y. split; intros H.
    - intros z H'. unfold elem. unfold incl. simpl. split.
        + simpl. apply incl_n_Nil.
        + unfold incl in H. destruct x as [|x xs].
            { admit. }
            { simpl in H.  apply elem_toList in H'.
              destruct H as [H1 [y1 [H2 [H3 H4]]]].
              destruct H' as [y2 [H5 [H6 H7]]].
              simpl in H5. destruct H5 as [H5|H5].
                { admit. (* not obvious *) }
                {

Show.
*)
