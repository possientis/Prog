Require Import List.

Require Import Utils.Ord.

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

(* 'Sorted' means by decreasing order                                           *)
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
    intros a o. induction xs as [|x xs IH].
    - simpl. constructor.
    - simpl. apply insertSorted. assumption.
Qed.