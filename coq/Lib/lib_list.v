Require Import List.

Lemma nil_or_not_nil : forall (A:Type)(l:list A),
  l = nil \/ l <> nil.
Proof.
  intros A l. elim l. left. reflexivity. clear l.
  intros a l. intros. right. unfold not. intros. discriminate.
Qed.


(* This lemma is part of the Coq 8.5 library *)
Lemma length_zero_iff_nil : forall (A:Type) (l:list A),
  length l = 0 <-> l = nil.
Proof.
  intros A l. elim l. unfold length. split; auto. 
  clear l. intros a l H. split. clear H. simpl. intro H.
  discriminate H. clear H. intro H. discriminate H.
Qed.

Lemma length_of_tl : forall (A:Type) (l: list A),
  l <> nil -> S (length (tl l)) = length l.
Proof.
  intros A l. elim l. unfold not. intro H. apply False_ind. auto.
  clear l. intros a l IH. intro H. clear H. simpl. reflexivity.
Qed.


