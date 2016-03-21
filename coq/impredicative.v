Set Implicit Arguments.

Definition myTrue : Prop := forall P:Prop, P->P.

Definition myFalse: Prop := forall P:Prop, P.
(* It can be shown that no proof of myFalse exists from empty context *)


Theorem myTrue_holds: myTrue.
Proof.
  intros P p; assumption.
Qed.

Theorem myFalse_ind: forall P:Prop, myFalse -> P.
Proof.
  intros P H. apply H.   
Qed.

Definition myNot (P:Prop) : Prop := P->myFalse.

Lemma L1 : myNot myFalse.
Proof.
  unfold myNot. intro H. exact H.
Qed.

Lemma Logic1: forall P:Prop, P->P.
Proof.
  intro P. intro H. exact H.
Qed.

Lemma L1' : myNot myFalse.
Proof.
  unfold myNot. apply Logic1.
Qed.






