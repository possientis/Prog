(* NEXT: ===> Trans                                                             *)

Require Import Le.
Require Import List.
Require Import Plus.

Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Order.
Require Import Core.Core.
Require Import Core.Incl.
Require Import Core.Elem.

(* A this stage of the development, both the inclusion relation <== and the     *)
(* membership relation :: have been defined. However, although we have ensured  *)
(* that the equivalence 'x :: y <-> {x} <== y' is true by definition, we still  *)
(* know very little about these two relations and a lot of work is required to  *)
(* prove many other expected properties so as to vindicate our choice of        *)
(* definitions. One such property is the transitivity of the inclusion relation *)
(* which will be established in the next module. For now, we look at two        *)
(* difficult and crucially important lemmas: the first one establishes a formal *)
(* link between the membership statement 'x :: xs' and the Coq statement        *)
(* 'In y (toList xs)'. Of course it is not true that if x is an element of xs   *)
(* then x should be an element of (toList xs). However, there should exists a y *)
(* in (toList xs) which is 'equivalent' to x in the sense of double inclusion.  *)
Lemma toListElem : forall (x xs:set), x :: xs <-> 
    exists (y:set), In y (toList xs) /\ (x <== y) /\ (y <== x).
Proof.
    intros x xs. split.
    - intros H. unfold elem in H. unfold incl in H. simpl in H.
      destruct H as [_ [y [H1 [H2 H3]]]]. exists y. split.
        + assumption.
        + split.
            { apply incl_n_incl with (max (order x) 0 + order xs).
                { apply le_trans with (order x + order xs).
                    { apply plus_le_compat_l. apply orderToList. assumption. }
                    { apply plus_le_compat_r. apply n_le_max. }}
                { assumption. }}
            { apply incl_n_incl with (max (order x) 0 + order xs).
                { rewrite plus_comm.
                  apply le_trans with (order x + order xs).
                    { apply plus_le_compat_l. apply orderToList. assumption. }
                    { apply plus_le_compat_r. apply n_le_max. }}
                { assumption. }}
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
                              apply orderToList. assumption. }
                            { apply plus_le_compat_r. apply n_le_max. }}
                        { assumption. }} 
                    { apply incl_incl_n. 
                        { rewrite plus_comm.
                          apply le_trans with (order x + order xs).
                            { apply plus_le_compat_l. 
                              apply orderToList. assumption. }
                            { apply plus_le_compat_r. apply n_le_max. }}
                        { assumption. }}}}
Qed.

Lemma toListIncl : forall (xs ys:set), xs <== ys <->
    (forall (z:set), In z (toList xs) -> z :: ys).
Proof.
    intros xs. induction xs as [|x _ xs IH]. 
    - intros ys. split.
        + intros H1 z H2. inversion H2.
        + intros. apply inclNil.
    - intros ys. split.
        + intros H1 z H2. unfold incl in H1. simpl in H1.
          destruct H1 as [H1 [y [H3 [H4 H5]]]].
          destruct H2 as [H2|H2].
            { subst. apply toListElem. exists y. split.
                { assumption. }
                { split.
                    { apply incl_n_incl 
                      with (max (order z) (order xs) + (order ys)).
                        { apply le_trans with (order z + order ys).
                            { apply plus_le_compat_l. apply orderToList.
                              assumption. }
                            { apply plus_le_compat_r. apply n_le_max. }}
                        { assumption. }}
                    { apply incl_n_incl 
                      with (max (order z) (order xs) + (order ys)).
                        { rewrite plus_comm.
                            apply le_trans with (order z + order ys).
                                { apply plus_le_compat_l. apply orderToList.
                                  assumption. }
                                { apply plus_le_compat_r. apply n_le_max. }}   
                        { assumption. }}}}
            { apply IH.
                { apply incl_n_incl 
                  with (max (order x) (order xs) + (order ys)).
                    { apply plus_le_compat_r. apply m_le_max. }
                    { assumption. }}
                { assumption. }}
        + intros H. unfold incl. simpl. split.
            { apply incl_incl_n.
                { apply plus_le_compat_r. apply m_le_max. }
                { apply IH. intros z H'. apply H. right. assumption. }}
            { assert (x :: ys) as H'.
                { apply H. left. reflexivity. }
                { apply toListElem in H'. destruct H' as [y [H1 [H2 H3]]].
                  exists y. split.
                    { assumption. }
                    { split.
                        { apply incl_incl_n.
                            { apply le_trans with (order x + order ys).
                                { apply plus_le_compat_l. apply orderToList.
                                  assumption. }
                                { apply plus_le_compat_r. apply n_le_max. }}   
                            { assumption . }}
                        { apply incl_incl_n.
                            { rewrite plus_comm.
                              apply le_trans with (order x + order ys).
                                { apply plus_le_compat_l. apply orderToList.
                                  assumption. }
                                { apply plus_le_compat_r. apply n_le_max. }}
                            { assumption. }}}}}    
Qed.
