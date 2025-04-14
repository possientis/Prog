Require Import set.
Require Import belong.
Require Import subset.
Require Import empty.
Require Import singleton.
Require Import union.

Definition succ (x:set) : set := union x (singleton x).

Proposition subset_a_succ_a : forall a:set, subset a (succ a).
Proof.
  intros a. apply union_left.
Qed.

Proposition belong_a_succ_a : forall a:set, a:(succ a).
Proof.
  intros. apply (union_right a). apply singleton_belong. reflexivity.
Qed.

Proposition belong_succ_O: forall a:set,
  a:(succ O) <-> a = O.
Proof.
  intros a. split. intros Ha. unfold succ in Ha.
  apply union_elim2 in Ha. elim Ha.
  clear Ha. intro Ha. apply False_ind. apply (empty_O a). exact Ha.
  clear Ha. intro Ha. apply singleton_belong. exact Ha.
  intro Ha. rewrite Ha. apply belong_a_succ_a.
Qed.

Proposition succ_O : succ O = singleton O.
Proof.
  unfold succ. rewrite union_O_a. reflexivity.
Qed.

(*
Proposition subset_succ_O: forall a:set,
  subset a (succ O) <-> a = O \/ a = succ O.
Proof.
  intros a. split.
  intros Ha.

Show.
*)
