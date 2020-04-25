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
            { intros H4. destruct (insertEquiv a o y xs) as [H5 H6].
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
        + rewrite <- sortIn. assumption.
        + assumption.
Qed.

Lemma equalHead : forall (a:Type) (o:Ord a) (x y:a) (xs ys:list a),
    Equiv (cons x xs) (cons y ys) ->
    Sorted (cons x xs) ->
    Sorted (cons y ys) ->
    x = y.
Proof.
    intros a o x y xs ys [H1 H2] H3 H4. destruct (eqDec x y) as [H5|H5].
    - assumption.
    - apply leqAsym.
        + apply sortedLeq with ys.
            { assumption. }
            { assert (In x (cons y ys)) as H6.
                { apply H1. left. reflexivity. }
              destruct H6 as [H6|H6].  
                { exfalso. apply H5. symmetry. assumption. }
                { assumption. }}
        + apply sortedLeq with xs.
            { assumption. }
            { assert (In y (cons x xs)) as H6.
                { apply H2. left. reflexivity. }
              destruct H6 as [H6|H6].  
                  { exfalso.  apply H5. assumption. }
                  { assumption. }}
Qed.

Lemma equivSortedNubed : forall (a:Type) (o:Ord a) (xs ys:list a),
    Nubed xs ->
    Nubed ys ->
    Sorted xs -> 
    Sorted ys -> 
    Equiv xs ys -> 
    xs = ys.
Proof.
    intros a o xs ys H. revert ys. induction H as [|x xs H1 H2 IH]; 
    intros ys H3 H4 H5 H6.
    - symmetry. apply EquivSym in H6. apply equivNil. assumption.
    - destruct ys as [|y ys].
        + apply equivNil. assumption.
        + assert (xs = ys) as H7.
            { apply IH.
                { apply (nubedConsTail a _ y). assumption. }
                { apply sortedConsTail with x. assumption. }
                { apply sortedConsTail with y. assumption. }
                { split; intros u H8.
                    { assert (In u (cons y ys)) as H9. 
                        { apply H6. right.  assumption. }
                      destruct H9 as [H9|H9].
                        { subst. exfalso. apply H1. 
                            assert (x = u) as H10.
                                { apply (equalHead a o _ _ xs ys); assumption. }
                          subst. assumption. }
                        { assumption. }}
                    { assert (In u (cons x xs)) as H11.
                        { destruct H6 as [H6 H12]. apply H12. right. assumption. }
                      destruct H11 as [H11|H11].
                        { assert (x = y).
                            { apply (equalHead a o _ _ xs ys); assumption. }
                          subst. exfalso. apply (nubedConsNotIn a _ y ys) in H3.
                          apply H3. assumption. }
                        { assumption. }}}}
          assert (x = y) as H8. { apply (equalHead a o _ _ xs ys); assumption. }
          subst. reflexivity. 
Qed.


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
