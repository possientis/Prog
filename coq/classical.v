Definition peirce                 := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic                := forall P:Prop, ~~P->P.
Definition excluded_middle        := forall P:Prop, P\/~P.
Definition de_morgan_not_and_not  := forall P Q:Prop, ~(~P/\~Q)->P\/Q.
Definition implies_to_or          := forall P Q:Prop, (P->Q)->(~P\/Q).

(* these five propositions are equivalent. Before we engage in the proof
of this equivalence, we shall clarify a few results, which do hold outside
of classical logic *)

(* this is the reverse of peirce, not very interesting *)
Lemma L1 : forall P Q: Prop, P->((P->Q)->P).
Proof.
  intros P Q Hp; intro Hpq; exact Hp.
Qed.

(* this is the reverse of classic *)
Lemma L2 : forall P:Prop, P->~~P.
Proof.
  intros P Hp; intro H; apply H; exact Hp.
Qed.

(* this is the reverse of de_morgan_not_and_not *)
Lemma L3 : forall P Q:Prop, P\/Q->~(~P/\~Q).
Proof.
  intros P Q H; intro H'; elim H'; intros Hnp Hnq.
  elim H.
  intro Hp; apply Hnp; exact Hp.
  intro Hq; apply Hnq; exact Hq.
Qed.

(* this is the reverse of implies_to_or *)
Lemma L4 : forall P Q: Prop, (~P\/Q)->(P->Q).
Proof.
  intros P Q H Hp. elim H. intro Hnp.
  apply False_ind. apply Hnp; exact Hp.
  intro Hq; exact Hq.
Qed.

Theorem peirce_to_classic : peirce->classic.
Proof.
  unfold peirce. unfold classic.
  intro H. intro P. intro H'.
  cut ((P->False)->P). intro H0.
  apply H with (Q:=False). exact H0.
  intro H1. apply False_ind. apply H'. exact H1.
Qed.

Theorem classic_to_excluded_middle : classic->excluded_middle.
Proof.
  unfold classic. unfold excluded_middle.
  intro H. intro P. apply H with (P:=P\/~P).
  intro H'. cut (~~P). intro H0. cut (~P).
  intro Hp. apply H0. exact Hp. intro Hp. apply H'.
  left; exact Hp. intro H1. apply H'. right; exact H1.
Qed.

Theorem excluded_middle_to_de_morgan : excluded_middle->de_morgan_not_and_not.
Proof.
  unfold excluded_middle. unfold de_morgan_not_and_not.
  intro ExM. intros P Q. intro H. cut ((P\/Q) \/~(P\/Q)).
  intro H0. elim H0. intro H1. exact H1. intro H2.
  apply False_ind. apply H. split. intro Hp. apply H2.
  left; exact Hp. intro Hq. apply H2. right; exact Hq. apply ExM.
Qed.


Theorem de_morgan_to_implies_to_or : de_morgan_not_and_not->implies_to_or.
Proof.
  unfold de_morgan_not_and_not. unfold implies_to_or.
  intro H. intros P Q. intro Hpq. cut(P\/~P). intro H1.
  elim H1. intro Hp. right. apply Hpq; exact Hp.
  intro H2. left; exact H2. apply H. intro H3. elim H3.
  intros H4 H5. apply H5; exact H4.
Qed.

Theorem implies_to_or_to_peirce : implies_to_or->peirce.
Proof.
  unfold implies_to_or. unfold peirce. intro H. intros P Q.
  intro H'. cut (~P\/P). intro H0. elim H0. intro H1.
  apply H'. intro Hp. apply False_ind. apply H1. exact Hp.
  intro Hp; exact Hp. apply H. intro Hp; exact Hp.
Qed.

