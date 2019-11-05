Require Import Le.
Require Import List.

Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Empty.
Require Import Core.ToList.
Require Import Core.ElemIncl.
Require Import Core.Decidability.
Require Import Core.Extensionality.

Fixpoint rank (xs:set) : nat :=
    match xs with 
    | Nil       => 0
    | Cons x xs => 
       match rank xs with
        | 0     => S (rank x)
        | S r   => S (max (rank x) r)
        end 
    end.
(* The rank is 0 if and only if the set is empty                                *)
Lemma rankNil : forall (x:set), rank x = 0 <-> x = Nil.
Proof.
    intros x. destruct x as [|x xs]; split.
    - intros. reflexivity.
    - intros. reflexivity.
    - simpl. destruct (rank xs) as [|n]; intros H; inversion H.
    - intros H. inversion H.
Qed.

(* When not empty, the rank is 1 + the maximum of the ranks of the elements     *)
Lemma rankMaximum : forall (x:set), x <> Nil -> 
    rank x = S (maximum (map rank (toList x))).
Proof.
    induction x as [|x IH1 xs IH2].
    - intros H. exfalso. apply H. reflexivity.
    - simpl. intros _. destruct (rank xs) as [|n] eqn:E.
        + apply rankNil in E. rewrite E. simpl. rewrite max_n_0. reflexivity.
        + assert (xs <> Nil) as H'.
            { intros H1. rewrite H1 in E. inversion E. }
          apply IH2 in H'. inversion H'. reflexivity.
Qed.

Lemma rankToList : forall (x xs:set), In x (toList xs) -> rank x < rank xs.
Proof.
    intros x xs H. destruct (set_eq_dec xs Nil) as [H'|H']. 
    - rewrite H' in H. inversion H.
    - rewrite (rankMaximum xs).
        + unfold lt. apply le_n_S. apply maximum_ubound. apply in_map_iff.
          exists x. split.
            { reflexivity. }
            { assumption. }
        + assumption.
Qed.

Lemma rankEqual : forall (x y:set), x == y -> rank x = rank y.
Proof.
    intros x y. remember (rank x) as n eqn:E. 
    assert (rank x <= n) as H. { rewrite E. apply le_n. }
    rewrite E. clear E. revert n x y H.  
    induction n as [|n IH]. (* induction on n, rank x <= n *)
    - intros x y H1 H2. apply le_0 in H1. apply rankNil in H1.
      rewrite H1 in H2. apply equal_sym in H2. apply emptyIsNil in H2.
      rewrite H1, H2. reflexivity.
    - intros x y H E. apply doubleIncl in E. destruct E as [E1 E2].
      apply le_antisym.
        + destruct (equal_dec x Nil) as [H1|H1].
            { apply emptyIsNil in H1. rewrite H1 in E1. rewrite H1 in E2.
              assert (y == Nil) as E. { apply doubleIncl. split; assumption. }
              apply emptyIsNil in E. rewrite H1, E. apply le_n. }
            { rewrite rankMaximum with x.
                { rewrite rankMaximum with y.
                    { apply le_n_S. apply maximum_lub. intros m H2.
                      apply in_map_iff in H2. destruct H2 as [z [H2 H3]].
                      assert (z :: y) as H4.
                        { apply elemIncl with x.
                            { assumption. }
                            { apply toListElem. exists z. split.
                                { assumption. }
                                { split; apply incl_refl. }}}
                      apply toListElem in H4. destruct H4 as [z' [H4 [H5 H6]]].
                      rewrite <- H2. rewrite (IH z z').
                        { apply maximum_ubound. apply in_map_iff. 
                          exists z'. split.
                            { reflexivity. }
                            { assumption. }}
                        { apply le_S_n. apply le_trans with (rank x).
                            { apply rankToList. assumption. }
                            { assumption. }}
                        { apply doubleIncl. split; assumption. }}
                    { intros H2. apply H1. rewrite <- H2. apply doubleIncl.
                      split; assumption. }}
                { intros H2. apply H1. rewrite H2. apply equal_refl. }}
        + destruct (equal_dec y Nil) as [H1|H1].
            { apply emptyIsNil in H1. rewrite H1 in E1. rewrite H1 in E2.
              assert (x == Nil) as E. { apply doubleIncl. split; assumption. }
              apply emptyIsNil in E. rewrite H1, E. apply le_n. }
            { rewrite rankMaximum with x.
                { rewrite rankMaximum with y.
                    { apply le_n_S. apply maximum_lub. intros m H2.
                      apply in_map_iff in H2. destruct H2 as [z [H2 H3]].
                      assert (z :: x) as H4.
                        { apply elemIncl with y.
                            { assumption. }
                            { apply toListElem. exists z. split.
                                { assumption. }
                                { split; apply incl_refl. }}}
                      apply toListElem in H4. destruct H4 as [z' [H4 [H5 H6]]].
                      rewrite <- H2. rewrite <- (IH z' z).
                        { apply maximum_ubound. apply in_map_iff.
                          exists z'. split.
                            { reflexivity. }
                            { assumption. }}
                        { apply le_S_n. apply le_trans with (rank x).
                            { apply rankToList. assumption. }
                            { assumption. }}
                        { apply doubleIncl. split; assumption. }}
                    { intros H2. apply H1. rewrite H2. apply equal_refl. }}
                { intros H2. apply H1. rewrite <- H2. apply doubleIncl.
                  split; assumption. }}
Qed.

Lemma rankElem : forall (x y:set), x :: y -> rank x < rank y.
Proof.
    intros x y H. apply toListElem in H. destruct H as [x' [H1 [H2 H3]]].
    rewrite (rankEqual x x').
    - apply rankToList. assumption.
    - apply doubleIncl. split; assumption.
Qed.


Lemma rankIncl : forall (x y:set), x <== y -> rank x <= rank y.
Proof.
    intros x y H. destruct (set_eq_dec x Nil) as [H1|H1].
    - rewrite H1. apply le_0_n.
    - rewrite (rankMaximum x).
        + rewrite (rankMaximum y).
            { apply le_n_S. apply maximum_lub. intros n H2.
              apply in_map_iff in H2. destruct H2 as [z [H2 H3]].
              assert (z :: y) as H4.
                { apply elemIncl with x.
                    { assumption. }
                    { apply toListElem. exists z. split.
                        { assumption. }
                        { split; apply incl_refl. }}}
                { rewrite <- H2. apply toListElem in H4.
                  destruct H4 as [z' [H4 [H5 H6]]]. rewrite (rankEqual z z').
                    { apply maximum_ubound. apply in_map_iff. exists z'. split.
                        { reflexivity. }
                        { assumption. }}
                    { apply doubleIncl. split; assumption. }}}
            { intros H2. apply H1. rewrite H2 in H. apply emptyIsNil.
              apply doubleIncl. split.
                { assumption. }
                { apply inclNil. }}
        + assumption.
Qed.

