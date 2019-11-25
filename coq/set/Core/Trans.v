(* NEXT: ===> ElemIncl                                                          *)

Require Import Le.
Require Import Plus.

Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Order.
Require Import Core.Core.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.ToList.

(* We have already established that out inclusion relation <== is reflexive.    *)
(* In this module, we tackle a far more difficult property, namely proving that *)
(* <== is a transitive relation. Obviously our definition would be useless if   *)
(* this property did not hold, so it is very important that we establish it. We *)
(* start with the inclusion statements which are relative to a natural number.  *)
Lemma incl_n_trans : forall (x y z:set) (n:nat),
    order x + order y + order z <= n ->
    incl_n n x y -> incl_n n y z -> incl_n n x z.
Proof.
    intros x y z n. revert x y z. induction n as [|n IH].
    - intros. apply I.
    - intros xs ys zs H1 H2 H3. destruct xs as [|x xs].
        + apply I.
        + simpl in H2. destruct H2 as [H2 [y [H4 [H5 H6]]]]. 
          simpl in H1. apply le_S_n in H1. simpl. split.
            { apply IH with ys.
                { apply weaken3_l with (max (order x) (order xs)).
                    { assumption. }
                    { apply m_le_max. }}
                { assumption. }
                { apply incl_le_m_n with (S n).
                    { apply weaken_l with (max (order x) (order xs) + order ys).
                        { assumption. }
                        { apply le_plus_r. }}
                    { apply le_S, le_n. }
                    { assumption. }}}
            { apply incl_n_incl in H3. 
                { rewrite toListIncl in H3.
                  assert (y :: zs) as H7. { apply H3. assumption. }
                  rewrite toListElem in H7.
                  destruct H7 as [z [H7 [H8 H9]]].
                  exists z. split.
                    { assumption. }
                    { split.
                        { apply (incl_incl_n y z n) in H8.
                            { apply IH with y.
                                { apply weaken_r with (order zs).
                                    { apply weaken3_m with (order ys).
                                        { apply weaken3_l 
                                          with (max (order x) (order xs)).
                                            { assumption. }
                                            { apply n_le_max. }}
                                        { apply orderToList. assumption. }}
                                    { apply orderToList. assumption. }}
                                { assumption. }
                                { assumption. }}
                            { apply le_trans with
                              (max (order x) (order xs) + order ys + order zs).
                                { rewrite <- plus_assoc.
                                  apply le_trans with (order ys + order zs).
                                    { apply le_trans with (order ys + order z).
                                        { apply plus_le_compat_r.
                                          apply orderToList. assumption. }
                                        { apply plus_le_compat_l.
                                          apply orderToList. assumption. }}
                                    { apply le_plus_r. }}
                                { assumption. }}}
                        { apply (incl_incl_n z y n) in H9.
                            { apply IH with y.
                                { remember (order z + order y) as e eqn:E.
                                  rewrite plus_comm. rewrite plus_comm in E.
                                  rewrite E. rewrite plus_assoc.
                                  apply weaken_r with (order zs).  
                                    { apply weaken3_m with (order ys).
                                        { apply weaken3_l
                                          with (max (order x) (order xs)).
                                            { assumption. }
                                            { apply n_le_max. }}
                                        { apply orderToList. assumption. }}
                                    { apply orderToList. assumption. }}
                                { assumption. }
                                { assumption. }}
                            { rewrite plus_comm.
                              apply le_trans with
                              (max (order x) (order xs) + order ys + order zs).
                                { rewrite <- plus_assoc.
                                  apply le_trans with (order ys + order zs).
                                    { apply le_trans with (order ys + order z).
                                        { apply plus_le_compat_r.
                                          apply orderToList. assumption. }
                                        { apply plus_le_compat_l.
                                          apply orderToList. assumption. }}
                                    { apply le_plus_r. }}
                                { assumption. }}}}}
                { apply le_S. apply le_trans
                  with (max (order x) (order xs) + order ys + order zs).
                      { rewrite <- plus_assoc. apply le_plus_r. }
                      { assumption. }}}
Qed.

(* We can now extend the previous results to inclusion statements proper.       *)
Theorem incl_trans : forall (x y z:set),
    x <== y -> y <== z -> x <== z.
Proof.
    intros x y z H1 H2.
    remember (order x + order y + order z) as n eqn:E.
    apply incl_n_incl with n.
    - rewrite <- plus_assoc in E. rewrite E.
      apply plus_le_compat_l. apply le_plus_r.  
    - apply incl_n_trans with y.
        + rewrite E. apply le_n. 
        + apply incl_incl_n.
            { rewrite E. apply le_plus_l. }
            { assumption. }
        + apply incl_incl_n.
            { rewrite <- plus_assoc in E. rewrite E.
              apply le_plus_r. }
            { assumption. }
Qed.
