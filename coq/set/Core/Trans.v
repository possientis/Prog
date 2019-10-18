Require Import Plus.

Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Order.
Require Import Core.Core.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.ToList.

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
            { apply incl_n_incl in H3. rewrite toListIncl in H3.
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
                                    { admit. }
                                    { apply orderToList. assumption. }}
                                { apply orderToList. assumption. }}
                            { assumption. }
                            { assumption. }}
                        { admit. }}
                    { apply (incl_incl_n z y n) in H9.
                        { apply IH with y.
                            { admit. }
                            { assumption. }
                            { assumption. }}
                        { admit. }}}
                    { admit. }}
Admitted.


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
