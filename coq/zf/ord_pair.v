Require Import set.
Require Import belong.
Require Import pair.
Require Import singleton.

(************************************************************************)
(*                          ordered pair                                *)
(************************************************************************)

(* (a,b) is defined as the pair {{a},{a,b}} *)
Definition ord_pair (a b:set) : set := { (singleton a), {a,b} }.

(* auxiliary lemma, no real value by itself *)
Lemma when_singleton_in_ord_pair : forall a a' b':set,
  belong (singleton a) (ord_pair a' b') -> a = a'.
Proof.
  intros a a' b' H. apply pair_elim in H. elim H.
  clear H. exact (singleton_injective a a').
  clear H. intros H. cut (belong a {a',b'} /\ a' = b').
  intros H'. elim H'. clear H'. intros H1 H2. apply pair_elim in H1. elim H1.
  clear H1. intros H1. exact H1.
  clear H1. intros H1. rewrite H2. exact H1. split.
  rewrite <- H. apply singleton_belong. reflexivity.
  apply when_pair_is_singleton with (c:=a). rewrite H. reflexivity.
Qed.

(* auxiliary lemma, no real value by itself *)
Lemma when_pair_in_ord_pair : forall a b a' b':set,
  belong {a,b} (ord_pair a' b')  -> a = b \/ {a,b} = {a',b'}.
Proof.
  intros a b a' b' H. apply pair_elim in H. elim H.
  clear H. intros H. left. apply when_pair_is_singleton with (c:= a'). exact H.
  clear H. intros H. right. exact H.
Qed.


Proposition ord_pair_left : forall a b a' b':set,
  ord_pair a b = ord_pair a' b' -> a = a'.
Proof.
  intros a b a' b' H. apply when_singleton_in_ord_pair with (b':=b'). 
  rewrite <- H. apply pair_left.
Qed.


Proposition ord_pair_right : forall a b a' b':set,
  ord_pair a b = ord_pair a' b' -> b = b'.
Proof.
  intros a b a' b' H. 
  cut (a = a'). intros Ha.
  cut (a = b \/ {a,b} = {a',b'}). intros H1.
  cut (a' = b'\/ {a',b'} = {a,b}). intros H2. elim H1. 
  clear H1. intro H1. elim H2.
  clear H2. intro H2. rewrite <- H1, <- H2. exact Ha.
  clear H2. intro H2. rewrite <- H1, Ha. 
  apply when_pair_is_singleton with (c:=a). rewrite <- H1 in H2. exact H2.
  clear H1. intro H1. clear H2.
  cut (b = a' \/ b = b'). intro H2.
  cut (b' = a \/ b' = b). intro H3. elim H2.
  clear H2. intro H2. elim H3.
  clear H3. intro H3. rewrite H2, H3, Ha. reflexivity.
  clear H3. intro H3. rewrite H3. reflexivity.
  clear H2. intro H2. exact H2. 
  apply pair_elim. rewrite H1. apply pair_right.
  apply pair_elim. rewrite <- H1. apply pair_right.
  apply when_pair_in_ord_pair. rewrite H. apply pair_right.
  apply when_pair_in_ord_pair. rewrite <- H. apply pair_right.
  apply ord_pair_left with (b:=b)(b':=b'). exact H.
Qed.
 

Proposition ordered_pair_injective: forall a b a' b':set,
  ord_pair a b = ord_pair a' b' -> a = a' /\ b = b'.
Proof.
  intros a b a' b' H. split. 
  apply ord_pair_left with (b:=b)(b':=b'). exact H.
  apply ord_pair_right with (a:=a)(a':=a'). exact H.
Qed.


