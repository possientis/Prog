Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Extensionality.

(*
Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.ToList.
Require Import Core.Extensionality.
*)

Definition union_ (xs ys:set) : set := fromList (toList xs ++ toList ys).

Lemma union_charac_ : forall (xs ys z:set), 
    z :: union_ xs ys <-> z :: xs \/ z :: ys.
Proof.
    induction xs as [|x _ xs IH]. 
    - intros ys z. split.
        + intros H. unfold union_ in H.
Show.
(*
    - intros ys z. unfold union_. simpl. split.
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
*)


