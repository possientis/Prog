Require Import Sets.Integers.
Require Import List.
Import Nat.

Require        Logic.List.Normal.

Require Import Logic.Nat.Max.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Cons.
Require Import Logic.Set.Rank.
Require Import Logic.Set.Equal.
Require Import Logic.Set.ToList.
Require Import Logic.Set.Extensionality.

Require Import Logic.Set.Normal.Map.
Require Import Logic.Set.Normal.Nub.
Require Import Logic.Set.Normal.Sort.
Require Import Logic.Set.Normal.Equiv.
Require Import Logic.Set.Normal.Insert.
Require Import Logic.Set.Normal.InListOf.

(* Nubing a sorted set yields a sorted set.                                     *)
Lemma nubSorted : forall (x:set), Sorted x -> Sorted (nub x).
Proof.
    intros x. unfold Sorted, nub. rewrite toListFromList.
    apply Normal.nubSorted.
Qed.

(* Inserting a set not already present into a nubed set, yields a nubed set.    *)
Lemma insertNubed : forall (x xs:set),
    ~ inListOf x xs -> Nubed xs -> Nubed (insert x xs).
Proof.
    intros x xs. rewrite insertCorrect. unfold inListOf, Nubed, insertAsList.
    rewrite toListFromList. apply Normal.insertNubed.
Qed.

(* Sorting a nubed set yields a nubed set.                                      *)
Lemma sortNubed : forall (x:set), Nubed x -> Nubed (sort x).
Proof.
    intros x. unfold Nubed, sort.
    rewrite toListFromList. apply Normal.sortNubed.
Qed.

(* Two sorted sets which are equivalent as lists have identical heads.          *)
Lemma sameHead : forall (x y xs ys:set),
    Equiv (Cons x xs) (Cons y ys) ->
    Sorted (Cons x xs) ->
    Sorted (Cons y ys) ->
    x = y.
Proof.
    intros x y xs ys. unfold Equiv, Sorted. simpl.
    apply Normal.sameHead.
Qed.

(* Two sorted and nubed sets which are equivalent as lists are identical.       *)
Lemma nubedSortedEquivSame : forall (x y:set),
    Nubed x ->
    Nubed y ->
    Sorted x ->
    Sorted y ->
    Equiv x y ->
    x = y.
Proof.
    intros x y. unfold Nubed, Sorted, Equiv.
    intros H1 H2 H3 H4 H5.
    rewrite <- (fromListToList x).
    rewrite <- (fromListToList y).
    assert (toList x = toList y) as H6.
        { apply (Normal.nubedSortedEquivSame _ _); assumption. }
    rewrite H6. reflexivity.
Qed.

(* Nubing and sorting commute with each other.                                 *)
Lemma nubSortCommute : forall (x:set), nub (sort x) = sort (nub x).
Proof.
    intros x. unfold nub, sort. rewrite toListFromList, toListFromList.
    rewrite Normal.nubSortCommute. reflexivity.
Qed.

(* Normalizing a set: recursive definition which is accepted by coq.            *)
Fixpoint normal (x:set) : set :=
    match x with
    | Nil       => Nil
    | Cons x xs => sort (nub (Cons (normal x) (normal xs)))
    end.

(* The real intended definition.                                                *)
Lemma normalDef : forall (x:set),
    normal x = sort (nub (map normal x)).
Proof.
    induction x as [|x IH1 xs IH2].
    - reflexivity.
    - simpl. apply nubedSortedEquivSame.
        + apply sortNubed, nubNubed.
        + apply sortNubed, nubNubed.
        + apply sortSorted.
        + apply sortSorted.
        + rewrite mapCons. apply sortEquivEquiv, nubEquivEquiv, equivConsCompat.
          rewrite IH2. apply equivTrans with (nub (map normal xs)).
            { apply sortEquiv. }
            { apply nubEquiv. }
Qed.

(* Predicate expressing the fact that a set is in normal form:                  *)
(* A set is in normal form when it has been nubed and sorted,                   *)
(* and every element of its list is itself in normal form.                      *)
Inductive Normal (x:set) : Prop :=
| mkNormal :
    Nubed x  ->
    Sorted x ->
    (forall (z:set), inListOf z x -> Normal z) ->
    Normal x
.

(* A set is equal to its normal form, not identical, not equivalent as list.    *)
Lemma normalEqual : forall (x:set), normal x == x.
Proof.
    induction x as [|x IH1 xs IH2].
    - apply equalRefl.
    - unfold normal. fold normal.
      apply sortEqual', nubEqual', consCompatLR; assumption.
Qed.

(* The normal form has same rank                                                *)
Lemma normalRank : forall (x:set), rank (normal x) = rank x.
Proof.
    intros x. apply rankEqual, normalEqual.
Qed.

(* The normal form is nubed.                                                    *)
Lemma normalNubed : forall (x:set), Nubed (normal x).
Proof.
    intros x. rewrite normalDef. apply sortNubed, nubNubed.
Qed.

(* The normal form is sorted.                                                   *)
Lemma normalSorted : forall (x:set), Sorted (normal x).
Proof.
    intros x. rewrite normalDef. apply sortSorted.
Qed.

(* The empty set is in normal form.                                             *)
Lemma NilNormal : Normal Nil.
Proof.
    constructor.
    - constructor.
    - constructor.
    - intros z H. inversion H.
Qed.

(* The normal form is in normal form.                                           *)
Lemma normalNormal : forall (x:set), Normal (normal x).
Proof.
    (* Setting up induction on rank x.                                          *)
    intros x. remember (rank x) as n eqn:E.
    assert (rank x <= n) as H. { rewrite E. apply le_n. }
    clear E. revert H. revert x. revert n.
    (* Actual proof.                                                            *)
    induction n as [|n IH]; intros x H1.
    - inversion H1 as [H2|]. apply rankNil in H2. rewrite H2. apply NilNormal.
    - constructor.
        + apply normalNubed.
        + apply normalSorted.
        + intros z H2. rewrite normalDef in H2.
          apply sortInListOfIff, nubInListOfIff in H2.
          apply inListOfMapIff in H2. destruct H2 as [z' [H2 H3]].
          rewrite <- H2. apply IH. apply rankToList in H3.
          apply le_S_n. apply le_trans with (rank x); assumption.
Qed.

(* Two equal sets in normal form are syntactically the same.                    *)
Lemma normalEqualSame : forall (x y:set),
    Normal x -> Normal y -> x == y -> x = y.
Proof.
    (* Setting up induction on max (rank x) (rank y).                           *)
    intros x y. remember (max (rank x) (rank y)) as n eqn:E.
    assert (rank x <= n) as H1. { rewrite E. apply n_le_max. }
    assert (rank y <= n) as H2. { rewrite E. apply m_le_max. }
    clear E. revert H1 H2. revert x y. revert n.
    (* Actual proof.                                                            *)
    induction n as [|n IH]; intros x y Rx Ry Nx Ny E.
    - inversion Rx as [H1|]. inversion Ry as [H2|].
      apply rankNil in H1. apply rankNil in H2. subst. reflexivity.
    - destruct Nx as [H1 H2 H3]. destruct Ny as [H4 H5 H6].
      apply nubedSortedEquivSame; try (assumption).
      clear H1 H2 H4 H5. rename H3 into H1. rename H6 into H2.
      rewrite doubleIncl in E. destruct E as [E1 E2].
      split; intros z H3.
        + assert (z :: y) as H4. { apply toListIncl with x; assumption. }
          rewrite toListElem in H4. destruct H4 as [z' [H4 [H5 H6]]].
          assert (z = z') as H7.
            { apply IH.
                { apply le_S_n. apply le_trans with (rank x).
                    { apply rankToList. assumption. }
                    { assumption. }}
                { apply le_S_n. apply le_trans with (rank y).
                    { apply rankToList. assumption. }
                    { assumption. }}
                { apply H1, H3. }
                { apply H2, H4. }
                { apply doubleIncl. split; assumption. } }
            rewrite H7. assumption.
        + assert (z :: x) as H4. { apply toListIncl with y; assumption. }
          rewrite toListElem in H4. destruct H4 as [z' [H4 [H5 H6]]].
          assert (z = z') as H7.
            { apply IH.
                { apply le_S_n. apply le_trans with (rank y).
                    { apply rankToList. assumption. }
                    { assumption. }}
                { apply le_S_n. apply le_trans with (rank x).
                    { apply rankToList. assumption. }
                    { assumption. }}
                { apply H2, H3. }
                { apply H1, H4. }
                { apply doubleIncl. split; assumption. }}
          rewrite H7. assumption.
Qed.

(* The predicate Normal has the right semantics in relation to normal.          *)
(* A set is in normal form if and only if it is equal to its normal form.       *)
Lemma normalCheck : forall (x:set), Normal x <-> normal x = x.
Proof.
    intros x. split; intro H.
    - apply normalEqualSame.
        + apply normalNormal.
        + assumption.
        + apply normalEqual.
    - rewrite <- H. apply normalNormal.
Qed.

(* Equality between sets equivalent to syntactic equality of their normal forms.*)
Lemma normalCharac : forall (x y:set),
    x == y <-> normal x = normal y.
Proof.
    intros x y. split; intros H.
    - apply normalEqualSame.
        + apply normalNormal.
        + apply normalNormal.
        + apply equalTrans with x.
            { apply normalEqual. }
            { apply equalTrans with y.
                { assumption. }
                { apply equalSym, normalEqual. }}
    - apply equalTrans with (normal x).
        + apply equalSym, normalEqual.
        + rewrite H. apply normalEqual.
Qed.
