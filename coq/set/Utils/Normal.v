Require Import List.

Require Import Utils.Nub.
Require Import Utils.Ord.
Require Import Utils.Sort.

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
            { destruct (in_dec eqDec x xs) as [H5|H5].
                {

Show.


(*
(* is this true ? *)
Lemma nubInInsert : forall (a:Type) (o:Ord a) (x:a) (xs:list a),
    In x xs -> nub (insert x xs) = nub xs.
Proof.
    intros a o x xs. revert x. induction xs as [|x xs IH]; intros y H.
    - inversion H.
    - simpl.  destruct H as [H|H].
        + subst. destruct (leqDec y y) as [H1|H1].
            { destruct (in_dec eqDec y xs) as [H2|H2].
                { simpl. destruct (in_dec eqDec y (insert y xs)) as [H3|H3].
                    { apply IH. assumption. }
                    { exfalso. apply H3. apply insertIn. }}
                { simpl. destruct (in_dec eqDec y (insert y xs)) as [H3|H3]. 
                    { clear H1. clear H3.


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