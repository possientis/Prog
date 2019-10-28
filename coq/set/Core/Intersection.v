Require Import List.

Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Filter.
Require Import Core.Decidability.
Require Import Core.Extensionality.


Definition in_set (x:set) : set -> Prop := (fun (z:set) => z :: x).

Definition in_set_dec (x:set) : Dec (in_set x) := (fun (z:set) => elem_dec z x).

Definition inter (x y:set) : set := fromList (filter (in_set_dec y) (toList x)). 

Notation "x /\ y" := (inter x y) : set_scope.

(*
Lemma inter_charac : forall (xs ys z:set),
    z :: (xs /\ ys) <-> z :: xs /\ z :: ys.
Proof.
    induction xs as [|x _ xs IH].
    - admit.
    - intros ys z. split.
        + intros H. unfold inter in H. simpl in H.
          destruct (in_set_dec ys x) as [H'|H'].
            { simpl in H. apply consElem in H.


Show.
*)
