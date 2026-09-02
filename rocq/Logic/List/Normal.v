Require Import List.

Require Import Logic.Class.Ord.

Require Import Logic.List.In.
Require Import Logic.List.Nub.
Require Import Logic.List.Sort.
Require Import Logic.List.Equiv.

(* Nubing a sorted list yields a sorted list.                                   *)
Lemma nubSorted : forall (a:Type) (o:Ord a) (xs:list a),
    Sorted xs -> Sorted (nub xs).
Proof.
    intros a o xs H. induction H as [|x|x y xs H1 H2 IH]. 
    - constructor.
    - constructor.
    - simpl. destruct (eqDec x y) as [H3|H3].
        + subst. exact IH.
        + destruct (in_dec eqDec y xs) as [H4|H4].
            { exact IH. }
            { simpl in IH. destruct (in_dec eqDec x xs) as [H5|H5].
                { apply sortedCons.
                    { intros z H6. apply leqTrans with x.
                        { apply sortedConsInLeq with xs.
                            { assumption. }
                            { rewrite nubInIff. exact H6. }} (* assumption fails *)
                        { assumption. }}
                    { assumption. }}
                { apply sortedCons.
                    { intros z [H6|H6].
                        { subst. assumption. }
                        { apply leqTrans with x.
                            { apply sortedConsInLeq with xs.
                                { assumption. }
                                { rewrite nubInIff. exact H6. }}
                            { assumption. }}}
                    { assumption. }}}
Qed.

(* Inserting a new element into a nubed list yields a nubed list.               *)
Lemma insertNubed : forall (a:Type) (o:Ord a) (x:a) (xs:list a),
    ~ x :: xs -> Nubed xs -> Nubed (insert x xs).
Proof.
    intros a o x xs H1 H. revert H1. revert x.
    induction H as [|x xs H1 H2 IH]; intros y H; simpl.
    - constructor.
        + assumption.
        + constructor.
    - destruct (leqDec y x) as [H3|H3].
        + constructor.
            { intros H4. destruct (insertEquivCons a o y xs) as [H5 H6].
              apply (H5 x) in H4. destruct H4 as [H4|H4].
                { subst. apply H. left. reflexivity. }
                { apply H1.  assumption. }}
            { apply IH. intros H4. apply H. right. assumption. }
        + constructor.
            { assumption. }
            { constructor; assumption. }
Qed.

(* Sorting a nubed list yields a nubed list.                                    *)
Lemma sortNubed : forall (a:Type) (o:Ord a) (xs:list a),
    Nubed xs -> Nubed (sort xs).
Proof.
    intros a o xs H. induction H as [|x xs H1 H2 IH]; simpl.
    - constructor.
    - apply insertNubed.
        + rewrite <- sortInIff. assumption.
        + assumption.
Qed.

(* Two sorted lists which are equivalent have identical heads.                  *)
Lemma sameHead : forall (a:Type) (o:Ord a) (x y:a) (xs ys:list a),
    cons x xs ==  cons y ys ->
    Sorted (cons x xs) ->
    Sorted (cons y ys) ->
    x = y.
Proof.
    intros a o x y xs ys [H1 H2] H3 H4. destruct (eqDec x y) as [H5|H5].
    - assumption.
    - apply leqAsym.
        + apply sortedConsInLeq with ys.
            { assumption. }
            { assert (In x (cons y ys)) as H6.
                { apply H1. left. reflexivity. }
              destruct H6 as [H6|H6].  
                { exfalso. apply H5. symmetry. assumption. }
                { assumption. }}
        + apply sortedConsInLeq with xs.
            { assumption. }
            { assert (In y (cons x xs)) as H6.
                { apply H2. left. reflexivity. }
              destruct H6 as [H6|H6].  
                  { exfalso.  apply H5. assumption. }
                  { assumption. }}
Qed.

(* Two sorted and nubed lists which are equivalent are identical.               *)
Lemma nubedSortedEquivSame : forall (a:Type) (o:Ord a) (xs ys:list a),
    Nubed xs  ->
    Nubed ys  ->
    Sorted xs -> 
    Sorted ys -> 
    xs == ys  -> 
    xs = ys.
Proof.
    intros a o xs ys H. revert ys. induction H as [|x xs H1 H2 IH]; 
    intros ys H3 H4 H5 H6.
    - symmetry. apply equivSym in H6. apply equivNil. assumption.
    - destruct ys as [|y ys].
        + apply equivNil. assumption.
        + assert (xs = ys) as H7.
            { apply IH.
                { apply (nubedConsNubedTail a _ y). assumption. }
                { apply sortedConsSortedTail with x. assumption. }
                { apply sortedConsSortedTail with y. assumption. }
                { split; intros u H8.
                    { assert (In u (cons y ys)) as H9. 
                        { apply H6. right.  assumption. }
                      destruct H9 as [H9|H9].
                        { subst. exfalso. apply H1. 
                            assert (x = u) as H10.
                                { apply (sameHead a o _ _ xs ys); assumption. }
                          subst. assumption. }
                        { assumption. }}
                    { assert (In u (cons x xs)) as H11.
                        { destruct H6 as [H6 H12]. apply H12. right. assumption. }
                      destruct H11 as [H11|H11].
                        { assert (x = y).
                            { apply (sameHead a o _ _ xs ys); assumption. }
                          subst. exfalso. apply (nubedConsNotIn a _ y ys) in H3.
                          apply H3. assumption. }
                        { assumption. }}}}
          assert (x = y) as H8. { apply (sameHead a o _ _ xs ys); assumption. }
          subst. reflexivity. 
Qed.

(* Nubing and sorting commute with each other.                                  *) 
Lemma nubSortCommute : forall (a:Type) (o:Ord a) (xs:list a),
    nub (sort xs) = sort (nub xs).
Proof.
    intros a o xs. apply (nubedSortedEquivSame a _).
    - apply nubNubed.
    - apply sortNubed. apply nubNubed.
    - apply nubSorted. apply sortSorted.
    - apply sortSorted.
    - apply equivTrans with xs.
        + apply equivTrans with (sort xs).
            { apply nubEquiv.  }
            { apply sortEquiv. }
        + apply equivTrans with (nub xs).
            { apply equivSym. apply nubEquiv.  }
            { apply equivSym. apply sortEquiv. }
Qed.

(* Normalizing a list: simply sorting and nubing.                               *)
Definition normal (a:Type) (o:Ord a) (xs:list a) : list a := sort (nub xs). 

Arguments normal {a} {o}.

(* Predicate expressing the fact that a list is in normal form:                 *)
(* A list is in normal form when it has been nubed and sorted.                  *)
Definition Normal (a:Type) (o:Ord a) (xs:list a) : Prop := Nubed xs /\ Sorted xs. 

Arguments Normal {a} {o}.

(* A list is equivalent to its normal form                                      *)
Lemma normalEquiv : forall (a:Type) (o:Ord a) (xs:list a), normal xs == xs.
Proof.
    intros a o xs. unfold normal. apply equivTrans with (nub xs).
    - apply sortEquiv.
    - apply nubEquiv.
Qed.

(* The normal form is in normal form.                                           *)
Lemma normalNormal : forall (a:Type) (o:Ord a) (xs:list a), Normal (normal xs).
Proof.
    intros a o xs. unfold normal. split.
    - apply sortNubed. apply nubNubed.
    - apply sortSorted.
Qed.

(* Two equivalent lists in normal form are equal.                               *)
Lemma normalEquivSame : forall (a:Type) (o:Ord a) (xs ys:list a),
    Normal xs -> Normal ys -> xs == ys -> xs = ys.
Proof.
    intros a o xs ys [H1 H2] [H3 H4] H5. 
    apply (nubedSortedEquivSame a _); assumption.
Qed.


(* The predicate Normal has the right semantics in relation to normal.          *)
(* A list is in normal form if and only if it is equal to its normal form.      *)
Lemma normalCheck : forall (a:Type) (o:Ord a) (xs:list a),
    Normal xs <-> normal xs = xs.
Proof.
    intros a o xs. split; intro H.
    - apply (normalEquivSame a _).
        + apply normalNormal.
        + assumption.
        + apply normalEquiv.
    - rewrite <- H. apply normalNormal.
Qed.

(* Equivalence between lists is equivalent to equality of their normal forms.   *)
Lemma normalCharac : forall (a:Type) (o:Ord a) (xs ys:list a),
    xs == ys <-> normal xs = normal ys.
Proof.
    intros a o xs ys. split; intros H.
    - apply (normalEquivSame a _).
        + apply normalNormal.
        + apply normalNormal.
        + apply equivTrans with xs.
            { apply normalEquiv. }
            { apply equivTrans with ys.
                { assumption. }
                { apply equivSym, normalEquiv. }}
    - apply equivTrans with (normal xs).
        + apply equivSym, normalEquiv.
        + rewrite H. apply normalEquiv.
Qed.
