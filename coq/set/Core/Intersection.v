(* NEXT: ===> Powerset                                                          *) 


Require Import List.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Empty.
Require Import Core.Filter.
Require Import Core.ToList.
Require Import Core.Decidability.
Require Import Core.Extensionality.

(* In this module we shall define the intersection of two sets. The existence   *)
(* of such intersection is usually derived from existing ZF axioms, so there is *)
(* no specific axiom for intersection. However, in order for us to prove that   *)
(* the powerset axiom is true in our model (see in the next module), we need a  *)
(* notion of intersection. We start by defining a predicate on the type set.    *)
Definition in_set (x:set) : set -> Prop := (fun (z:set) => z :: x).


(* Having proved that set membership is decidable, so is our predicate 'in_set' *)
Definition in_set_dec (x:set) : Dec (in_set x) := (fun (z:set) => elem_dec z x).

(* We define the pairwise intersection x /\ y of x and y by restricting the     *)
(* list of elements of x to those which also belong to y.                       *)
Definition inter (x y:set) : set := fromList (filter (in_set_dec y) (toList x)). 

Notation "x /\ y" := (inter x y) : set_scope.

(* z belong to the intersection x /\ y if and only it belongs to both x and y.  *)
Lemma inter_charac : forall (xs ys z:set),
    z :: (xs /\ ys) <-> z :: xs /\ z :: ys.
Proof.
    induction xs as [|x _ xs IH].
    - intros ys z. unfold inter. simpl. split.
        + intros H. exfalso. apply emptyCharac with z. assumption.
        + intros [H1 H2]. assumption.
    - intros ys z. split.
        + intros H. unfold inter in H. simpl in H.
          destruct (in_set_dec ys x) as [H'|H'].
            { simpl in H. apply consElem in H. destruct H as [H|H].
                { split.
                    { apply consElem. left. assumption. }
                    { unfold in_set in H'. apply equal_l with x.
                        { apply equalSym. assumption. }
                        { assumption. }}}
                { apply IH in H. destruct H as [H1 H2]. split.
                    { apply consElem. right. assumption. }
                    { assumption. }}}
            { apply IH in H. destruct H as [H1 H2]. split.
                { apply consElem. right. assumption. }
                { assumption. }}
        + intros [H1 H2]. unfold inter. simpl.
          destruct (in_set_dec ys x) as [H'|H'].
            { apply consElem in H1. destruct H1 as [H1|H1]. 
                { apply toListElem. exists x. split.
                    { rewrite toListFromList. left. reflexivity. }
                    { apply doubleIncl. assumption. }}
                { assert (z :: (xs /\ ys)) as H3.
                    { apply IH. split; assumption. }
                  apply toListElem in H3. destruct H3 as [y [H3 H4]]. 
                  apply toListElem. exists y. split.
                    { rewrite toListFromList. right. unfold inter in H3.
                      rewrite toListFromList in H3. assumption. }
                    { assumption. }}}
            { apply consElem in H1. destruct H1 as [H1|H1].
                { exfalso. apply H'. unfold in_set. 
                  apply equal_l with z; assumption. }
                { apply IH. split; assumption. }}
Qed.
