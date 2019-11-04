Require Import List.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Empty.
Require Import Core.ToList.
Require Import Core.Pairing.
Require Import Core.Extensionality.

(* This definition will be shown to be strictly equivalent to the usual one     *)
Definition union2 (xs ys:set) : set := fromList (toList xs ++ toList ys).

Notation "x \/ y" := (union2 x y) : set_scope.

Lemma union2_charac : forall (xs ys z:set), 
    z :: (xs \/ ys) <-> z :: xs \/ z :: ys.
Proof.
    induction xs as [|x _ xs IH]. 
    - intros ys z. split.
        + intros H. unfold union2 in H. simpl in H. 
          rewrite fromListToList in H. right. assumption.
        + intros [H|H].
            { exfalso. apply emptyCharac in H. assumption. }
            { unfold union2. simpl. rewrite fromListToList. assumption. }
    - intros ys z. unfold union2. simpl. split.
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
    | Cons x xs => union2 x (union xs)
    end. 


Lemma union_charac : forall (xs z:set), 
    z :: union xs <-> exists (x:set), z :: x /\ x :: xs.
Proof.
    induction xs as [|x _ xs IH].
    - intros z. simpl. split.
        + intros H. exfalso. apply (emptyCharac z). assumption.
        + intros [x [H1 H2]]. exfalso. apply (emptyCharac x). assumption.
    - intros z. split.
        + simpl. intros H. apply union2_charac in H. destruct H as [H|H].
            { exists x. split.
                { assumption. }
                { apply consElem. left. apply equal_refl. }}
            { apply IH in H. destruct H as [y [H1 H2]]. exists y. split.
                { assumption. }
                { apply consElem. right. assumption. }}
        + simpl. intros H. destruct H as [x' [H1 H2]]. apply consElem in H2.
          destruct H2 as [H2|H2]; apply union2_charac.
            { left. rewrite extensionality in H2. apply H2. assumption. }
            { right. apply IH. exists x'. split; assumption. }
Qed.

(* Our definition of the union of two sets is strictly the usual one            *) 
Lemma union2_union : forall (x y:set), (x \/ y) = union {x,y}.
Proof.
    intros x y. unfold union2, pair, union, union2.
    rewrite toListFromList. simpl. rewrite app_nil_r. reflexivity.
Qed.

(* The union axiom is satisfied in 'set'                                        *)
Theorem union_axiom : forall (x:set), exists (y:set), forall (z:set),
    z :: y <-> exists (u:set), z :: u /\ u :: x.
Proof. intros x. exists (union x). apply union_charac. Qed.

