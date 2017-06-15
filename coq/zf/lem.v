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

Show.
