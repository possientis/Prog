Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Empty.
Require Import Core.ToList.
Require Import Core.Extensionality.


Definition union2_ (xs ys:set) : set := fromList (toList xs ++ toList ys).

Lemma union2_charac_ : forall (xs ys z:set), 
    z :: union2_ xs ys <-> z :: xs \/ z :: ys.
Proof.
    induction xs as [|x _ xs IH]. 
    - intros ys z. split.
        + intros H. unfold union2_ in H. simpl in H. 
          rewrite fromListToList in H. right. assumption.
        + intros [H|H].
            { exfalso. apply empty_charac in H. assumption. }
            { unfold union2_. simpl. rewrite fromListToList. assumption. }
    - intros ys z. unfold union2_. simpl. split.
        + intros H. apply consElem in H. destruct H as [H|H].
            { left. apply consElem. left. assumption. }
            { apply IH in H. destruct H as [H|H].
                { left. apply consElem. right. assumption. }
                { right. assumption. }}
        + intros [H|H].
            { apply consElem in H. destruct H as [H|H]; apply consElem.
                { left. assumption. }
                { right. apply IH. left. assumption. }}
            { apply consElem. right. apply IH. right. assumption. }
Qed.

Fixpoint union (xs:set) : set :=
    match xs with 
    | Nil       => Nil
    | Cons x xs => union2_ x (union xs)
    end. 


Lemma union_charac : forall (z xs:set), 
    z :: union xs <-> exists (x:set), z :: x /\ x :: xs.
Proof.
    intros z xs. revert z. induction xs as [|x _ xs IH].
    - admit.
    - intros z. split.
        + simpl. intros H. apply union2_charac_ in H. destruct H as [H|H].
            { exists x. split.
                { assumption. }
                { apply consElem. left. apply equal_refl. }}
            { apply IH in H. destruct H as [y [H1 H2]]. exists y. split.
                { assumption. }
                { apply consElem. right. assumption. }}
        + simpl. intros H.

Show.


