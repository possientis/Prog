Require Import List.

Require Import Utils.Ord.
Require Import Utils.Equiv.

(* Insert the element x inside the ordered list xs                              *)
Fixpoint insert (a:Type) (o:Ord a) (x:a) (xs:list a) : list a :=
    match xs with
    | nil       => cons x nil
    | cons y ys => 
        match (leqDec x y) with
        | left _    => cons y (insert a o x ys) (* x 'smaller' does inside      *)
        | right _   => cons x (cons y ys)
        end
    end.

Arguments insert {a} {o}.

(* Sorts a list by decreasing order                                             *)
Fixpoint sort (a:Type) (o:Ord a) (xs:list a) : list a :=
    match xs with
    | nil       => nil
    | cons x xs => insert x (sort a o xs)
    end.

Arguments sort {a} {o}.

(* 'Sorted' means by decreasing order: need Ord instance for 'leq'              *)
Inductive Sorted (a:Type) (o:Ord a) : list a -> Prop :=
| SortedNil    : Sorted a o nil
| SortedSingle : forall (x:a), Sorted a o (cons x nil)
| SortedCons   : forall (x y:a) (xs:list a), 
    leq x y -> Sorted a o (cons x xs) -> Sorted a o (cons y (cons x xs)) 
.

Arguments Sorted       {a} {o}.
Arguments SortedNil    {a} {o}.
Arguments SortedCons   {a} {o}.
Arguments SortedSingle {a} {o}.

(* Inserting an element into a sorted list leads to a sorted list.              *)
Lemma insertSorted : forall (a:Type) (o:Ord a) (x:a) (xs:list a),
    Sorted xs -> Sorted (insert x xs).
Proof.
    intros a o x xs H. revert x. induction H as [|x|x y xs H1 H2 IH]; intros u.
    - simpl. constructor.
    - simpl. destruct (leqDec u x) as [H'|H'].
        + constructor.
            { assumption. }
            { constructor. } 
        + constructor.
            { destruct (leqTotal u x) as [H1|H1].
                { apply H' in H1. contradiction. }
                { assumption. }}
            { constructor. }
    - simpl. simpl in IH. 
      destruct (leqDec u y) as [H3|H3].
        + remember (IH u) as H5 eqn:F. clear F. 
          destruct (leqDec u x) as [H4|H4] eqn:E; constructor; assumption.
        + constructor.
            { destruct (leqTotal u y) as [H6|H6].
                { apply H3 in H6. contradiction. }
                { assumption. }}
            { remember (IH y) as H5 eqn:F. clear F.
                destruct (leqDec y x) as [H7|H7].
                    { constructor; assumption. }
                    { assumption. }}
Qed.

(* Sorting a list leads to a sorted list.                                       *)
Lemma sortSorted : forall (a:Type) (o:Ord a) (xs:list a), Sorted (sort xs).
Proof.
    intros a o. induction xs as [|x xs IH]; simpl.
    - constructor.
    - apply insertSorted. assumption.
Qed.

Lemma insertIn : forall (a:Type) (o:Ord a) (x:a) (xs:list a), In x (insert x xs).
Proof.
    intros a o x xs. revert x. induction xs as [|x xs IH]; intros y; simpl.
    - left. reflexivity.
    - destruct (leqDec y x) as [H|H].
        + right. apply IH.
        + left. reflexivity.
Qed.

Lemma sortedLeq : forall (a:Type) (o:Ord a) (x y:a) (xs:list a),
    Sorted (cons x xs) -> In y xs -> leq y x.
Proof.
    intros a o x y xs H. remember (cons x xs) as ys eqn:E. revert E.
    revert xs x y. induction H as [|u|u v us H1 H2 IH]; intros xs x y H.
    - inversion H.
    - inversion H. intros H'. inversion H'.
    - inversion H. clear H. subst. intros [H3|H3].
        + subst. assumption.
        + apply leqTrans with u.
            { apply IH with us.
                { reflexivity. }
                { assumption. }}
            { assumption. }
Qed.

Lemma insertCons : forall (a:Type) (o:Ord a) (x:a) (xs:list a),
    Equiv (insert x xs) (cons x xs).
Proof.
    intros a o x xs. revert x. induction xs as [|x xs IH]; intros y.
    - apply EquivRefl.
    - simpl. destruct (leqDec y x) as [H|H].
        + split; intros z H1.
            { destruct H1 as [H1|H1].
                { subst. right. left. reflexivity. }
                { destruct (IH y) as [H2 H3]. destruct ((H2 z) H1) as [H4|H4].
                    { subst. left. reflexivity. }
                    { right. right. assumption. }}}
            { destruct H1 as [H1|H1].
                { subst. destruct (IH z) as [H2 H3]. right. apply H3.
                  left. reflexivity. }
                { destruct H1 as [H1|H1].
                    { subst. left. reflexivity. }
                    { right. destruct (IH y) as [H2 H3]. apply H3.
                      right. assumption. }}}
        + split; intros z H1; assumption.
Qed.

Lemma sortedEquiv : forall (a:Type) (o:Ord a) (xs:list a), Equiv xs (sort xs).
Proof.
    intros a o. induction xs as [|x xs [IH1 IH2]].
    - apply EquivRefl.
    - simpl. apply EquivTrans with (cons x (sort xs)).
        + split; intros z [H1|H1].
            { subst. left. reflexivity. }
            { right. apply IH1. assumption. }
            { subst. left. reflexivity. }
            { right. apply IH2. assumption. }
        + apply EquivSym. apply insertCons.
Qed.

Lemma sortedIn : forall (a:Type) (o:Ord a) (x:a) (xs:list a),
    In x xs <-> In x (sort xs).
Proof.
    intros a o x xs. destruct (sortedEquiv a o xs) as [H1 H2]. split; intros H.
    - apply H1. assumption.
    - apply H2. assumption.
Qed.

Lemma sortedCons : forall (a:Type) (o:Ord a) (x:a) (xs:list a),
    (forall (z:a), In z xs -> leq z x) -> Sorted xs -> Sorted (cons x xs).
Proof.
    intros a o x xs H1 H2. revert H1. revert x.
    induction H2 as [|x|x y xs H1 H2 IH]; intros z H.
    - constructor.
    - constructor.
        + apply H. left. reflexivity.
        + constructor.
    - constructor.
        + apply H. left. reflexivity.
        + apply IH. clear H. clear z. intros z [H3|H3].
            { subst. assumption. }
            { apply leqTrans with x.
                { apply sortedLeq with xs; assumption. }
                { assumption. }}
Qed.

Lemma insertLeq : forall (a:Type) (o:Ord a) (x:a) (xs:list a),
    (forall (y:a), In y xs -> leq y x) -> insert x xs = cons x xs.
Proof.
    intros a o x xs. revert x. induction xs as [|x xs IH]; intros y H.
    - reflexivity.
    - simpl. destruct (leqDec y x) as [H1|H1].
        + assert (x = y) as H2.
            { apply leqAsym.
                { apply H. left. reflexivity. }
                { assumption. }}
          subst. rewrite IH.
            { reflexivity. }
            { intros x H2. apply H. right. assumption. }
        + reflexivity.
Qed.

Lemma sortSame : forall (a:Type) (o:Ord a) (xs:list a),
    Sorted xs -> sort xs = xs.
Proof.
    intros a o xs H. induction H as [|x|x y xs H1 H2 IH].
    - reflexivity.
    - reflexivity.
    - simpl. simpl in IH. rewrite IH. simpl. destruct (leqDec y x) as [H3|H3].
        + destruct (eqDec x y) as [H4|H4].
            { subst. clear H1 H3. simpl. rewrite insertLeq.
                { reflexivity. }
                { intros x H3. apply sortedLeq with xs; assumption. }}
            { exfalso. apply H4. apply leqAsym; assumption. }
        + reflexivity.
Qed.

