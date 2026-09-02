Require Import Axiom_LEM.
Require Import logic.


Proposition or_and : forall p q:Prop, p\/q <-> ~(~p/\~q).
Proof.
  intros p q. split.
  apply or_not_and_not.
  intro H. cut (~(p\/q) \/ (p\/q)). intro H'. elim H'. 
  clear H'. intro H'. apply False_ind. apply H. split.
  intro H''. apply H'. left. exact H''.
  intro H''. apply H'. right. exact H''.
  intro H''. exact H''.
  apply law_excluded_middle.
Qed.

Proposition or_imp : forall p q:Prop, (p->q) <-> (~p\/q). 
Proof.
  intros p q. split.
  intro H. cut (~p\/p). intro H'. elim H'.
  clear H'. intro H'. left. exact H'.
  clear H'. intro H'. right. apply H. exact H'. 
  apply law_excluded_middle.
  apply not_P_or_imp.
Qed.

Proposition forall_exists : forall (A:Type)(P:A->Prop),
  (forall x:A, P x) <-> ~(exists x:A, ~P x).
Proof.
  intros A P. split.
  intros H. apply forall_not_exists. exact H.
  intros H a. cut(~P a\/P a). intro H'. elim H'.
  clear H'. intro H'. apply False_ind. apply H. exists a. exact H'.
  clear H'. intro H'. exact H'.
  apply law_excluded_middle.
Qed.



Proposition not_not : forall p:Prop, ~~p <-> p.
Proof.
  intros p. split.
  intros H. cut(~p\/p). intro H'. elim H'. 
  clear H'. intro H'. apply False_ind. apply H. exact H'.
  clear H'. intro H'. exact H'.
  apply law_excluded_middle.
  apply P_non_P. 
Qed.

Proposition peirce : forall p q:Prop, ((p->q)->p) <-> p.
Proof.
  intros p q. split.
  intro H. cut (~p\/p). intro H'. elim H'.
  clear H'. intro H'. apply H. apply or_imp. left. exact H'.
  clear H'. intro H'. exact H'.
  apply law_excluded_middle.
  apply peirce_reverse. 
Qed.

