(* NEXT: ===> Foundation                                                        *)

Require Import Sets.Integers.
Require Import List.
Import Nat.

Require Import Logic.Class.Eq.

Require Import Logic.Nat.Max.
Require Import Logic.Nat.Leq.
Require Import Logic.Nat.Minimal.
Require Import Logic.Nat.Maximum.

Require Import Logic.Set.Set.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.
Require Import Logic.Set.Empty.
Require Import Logic.Set.ToList.
Require Import Logic.Set.ElemIncl.
Require Import Logic.Set.Decidable.
Require Import Logic.Set.Extensionality.

Require Import Logic.Set.Normal.Ord.


(* Our next objective is to prove that the 'foundation axiom' is satisfied in   *)
(* our model. This will be carried out in the next module. However, in order    *)
(* for us to achieve this goal, we develop here the notion of 'rank' which is   *)
(* another measure of 'complexity' for a set, similar to the notion of 'order'  *)
(* which was presented in the Order module. Informally, the rank of a set xs is *)
(* defined as follows: 1. the rank of the empty set is 0. 2. the rank of a non- *)
(* empty set is 1 + the maximum of the ranks of its elements. However, in order *)
(* to convince Coq that our definition is well-founded, we need to express      *)
(* things in a more convoluted way. Luckily the lemma 'rankMaximum' below       *)
(* guarantees that our formal definition satisfies our informal description.    *)
Fixpoint rank (xs:set) : nat :=
    match xs with
    | Nil       => 0
    | Cons x xs =>
       match rank xs with
        | 0     => S (rank x)
        | S r   => S (max (rank x) r)
        end
    end.

(* The rank of a set is 0 if and only if the set is empty                       *)
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

(* If x lies in the list associated with xs, then it has a lesser rank.         *)
Lemma rankToList : forall (x xs:set), In x (toList xs) -> rank x < rank xs.
Proof.
    intros x xs H. destruct (eqDec xs Nil) as [H'|H'].
    - rewrite H' in H. inversion H.
    - rewrite (rankMaximum xs).
        + unfold lt. apply le_n_S. apply maximum_ubound. apply in_map_iff.
          exists x. split.
            { reflexivity. }
            { assumption. }
        + assumption.
Qed.

(* The notion of rank is actually compatible with our equivalence relation ==.  *)
Open Scope nat_scope.
Lemma rankEqual : forall (x y:set), x == y -> rank x = rank y.
Proof.
    intros x y. remember (rank x) as n eqn:E.
    assert (rank x <= n) as H. { rewrite E. apply le_n. }
    rewrite E. clear E. revert n x y H.
    induction n as [|n IH]. (* induction on n, rank x <= n *)
    - intros x y H1 H2. apply le_0 in H1. apply rankNil in H1.
      rewrite H1 in H2. apply equalSym in H2. apply emptyIsNil in H2.
      rewrite H1, H2. reflexivity.
    - intros x y H E. apply doubleIncl in E. destruct E as [E1 E2].
      apply le_antisymm.
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
                                { split; apply inclRefl. }}}
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
                { intros H2. apply H1. rewrite H2. apply equalRefl. }}
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
                                { split; apply inclRefl. }}}
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
                    { intros H2. apply H1. rewrite H2. apply equalRefl. }}
                { intros H2. apply H1. rewrite <- H2. apply doubleIncl.
                  split; assumption. }}
Qed.

(* If x is an element of y, then its rank is less than that of y.               *)
Lemma rankElem : forall (x y:set), x :: y -> rank x < rank y.
Proof.
    intros x y H. apply toListElem in H. destruct H as [x' [H1 [H2 H3]]].
    rewrite (rankEqual x x').
    - apply rankToList. assumption.
    - apply doubleIncl. split; assumption.
Qed.

(* If x is a subset of y, then its rank is less than or equal to that of y.     *)
(* Notation '<=' for set and nat are conflicting, using 'incl'.                 *)
Lemma rankIncl : forall (x y:set), incl x y -> rank x <= rank y.
Proof.
    intros x y H. destruct (eqDec x Nil) as [H1|H1].
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
                        { split; apply inclRefl. }}}
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


(* If a set is non-empty, it has an element of smallest rank.                   *)
Lemma rankMinimal : forall (x:set), x <> Nil ->
    exists (y:set), y :: x /\ forall (z:set), z :: x -> rank y <= rank z.
Proof.
    intros x H. remember (map rank (toList x)) as ns eqn:H1.
    assert (ns <> nil) as H2.
        { intros H2. apply H. destruct x as [| x xs].
            { reflexivity. }
            { rewrite H1 in H2. simpl in H2. inversion H2. }}
    destruct (natMinimal ns H2) as [n [H3 H4]]. rewrite H1 in H3.
    apply in_map_iff in H3. destruct H3 as [y [H3 H5]]. exists y. split.
    - apply toListElem. exists y. split.
        + assumption.
        + split; apply inclRefl.
    - intros z H6. rewrite H3. apply H4. apply toListElem in H6.
      destruct H6 as [z' [H6 [H7 H8]]]. rewrite H1. apply in_map_iff.
      exists z'. split.
        + apply rankEqual. apply doubleIncl. split; assumption.
        + assumption.
Qed.
