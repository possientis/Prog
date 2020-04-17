Require Import List.

Require Import Utils.Nub.
Require Import Utils.Ord.
Require Import Utils.Sort.
Require Import Utils.Equiv.


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
                        { apply sortedLeq with xs.
                            { assumption. }
                            { rewrite nubIn. exact H6. }} (* 'assumption' fails *)
                        { assumption. }}
                    { assumption. }}
                { apply sortedCons.
                    { intros z [H6|H6].
                        { subst. assumption. }
                        { apply leqTrans with x.
                            { apply sortedLeq with xs.
                                { assumption. }
                                { rewrite nubIn. exact H6. }}
                            { assumption. }}}
                    { assumption. }}}
Qed.


Lemma insertNubed : forall (a:Type) (o:Ord a) (x:a) (xs:list a),
    ~ In x xs -> Nubed xs -> Nubed (insert x xs).
Proof.
    intros a o x xs H1 H. revert H1. revert x.
    induction H as [|x xs H1 H2 IH]; intros y H; simpl.
    - constructor.
        + assumption.
        + constructor.
    - destruct (leqDec y x) as [H3|H3].
        + constructor.
            { intros H4. destruct (insertCons a o y xs) as [H5 H6].
              apply (H5 x) in H4. destruct H4 as [H4|H4].
                { subst. apply H. left. reflexivity. }
                { apply H1.  assumption. }}
            { apply IH. intros H4. apply H. right. assumption. }
        + constructor.
            { assumption. }
            { constructor; assumption. }
Qed.


Lemma sortNubed : forall (a:Type) (o:Ord a) (xs:list a),
    Nubed xs -> Nubed (sort xs).
Proof.
    intros a o xs H. induction H as [|x xs H1 H2 IH]; simpl.
    - constructor.
    - apply insertNubed.
        + rewrite <- sortedIn. assumption.
        + assumption.
Qed.

(*
Lemma nubSame : forall (a:Type) (o:Ord a) (xs ys:list a),
    Sorted xs -> Sorted ys -> Equiv xs ys -> nub xs = nub ys.
Proof.
    intros a o xs ys H. revert ys. 
    induction H as [|x|x y xs H1 H2 IH]; intros ys H3 H4.
    - admit.
    - admit.
    -
Show.
*)


(*
Lemma nubSortCommute : forall (a:Type) (o:Ord a) (xs:list a),
    nub (sort xs) = sort (nub xs).
Proof.
    intros a o. induction xs as [|x xs IH].
    - reflexivity.
    - simpl. destruct (in_dec eqDec x xs) as [H|H]. 
        +
Show.
*)
