(* NEXT: ===> Filter                                                            *) 


Require Import List.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Empty.
Require Import Core.ToList.
Require Import Core.Pairing.
Require Import Core.Extensionality.

(* In this module we shall prove that our model satisfies the 'union axiom'     *)
(* which is another commonly known axiom of ZF. This axiom essentially states   *)
(* the existence of a union set 'U x' given any set x. The union set U x is the *)
(* set obtained by collecting all the elements of the sets contained in x. So   *)
(* if you think of x as a set x = {y1, y2, y3, ... } then informally the union  *)
(* set U x is the union y1 \/ y2 \/ y3 \/ ... Hence in order for a set z to be  *)
(* an element of U x, it must be an element of a set y belonging to x. To show  *)
(* the existence of a union set in our model, we need to define it. We shall    *)
(* start by defining the union x \/ y of two sets x and y. The definition we    *)
(* provide here is not the standard definition encountered in set theory texts. *)
(* x \/ y is usually defined as U {x,y}, namely as the union set of the pair    *)
(* {x,y}. But of course we cannot follow this route here since we have not yet  *)
(* defined any notion of union set. Instead we use meta-theoretic constructs    *)
(* such as 'fromList' and 'toList' which are specific to our Coq model.         *)

Definition union2 (xs ys:set) : set := fromList (toList xs ++ toList ys).

Notation "x \/ y" := (union2 x y) : set_scope.

(* A set z is an element of the pairwise union xs \/ ys if and only if it is an *)
(* element of xs, *or* it is an element of ys.                                  *)
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

(* Now that we have defined the union of two sets, we can define the union set  *)
(* of a set xs, which is a fold over the elements of xs of the operator union2. *)
Fixpoint union (xs:set) : set :=
    match xs with 
    | Nil       => Nil
    | Cons x xs => union2 x (union xs)
    end. 

(* Our definition of union set satisfies the right property. A set z belongs    *)
(* to the union set of xs, if and only if it belongs to some x belonging to xs. *)
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

(* The union axiom is satisfied in our model: Every set x has a union set y.    *)
Theorem union_axiom : forall (x:set), exists (y:set), forall (z:set),
    z :: y <-> exists (u:set), z :: u /\ u :: x.
Proof. intros x. exists (union x). apply union_charac. Qed.

