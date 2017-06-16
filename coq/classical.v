Definition peirce                 := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic                := forall P:Prop, ~~P->P.
Definition lem                    := forall P:Prop, P\/~P.
Definition and_to_or              := forall P Q:Prop, ~(~P/\~Q)->P\/Q.
Definition imp_to_or              := forall P Q:Prop, (P->Q)->(~P\/Q).
Definition ex_to_all              := forall (A:Type) (P: A->Prop), 
                              ~(exists x:A, ~P x) -> (forall x:A, P x).

(* these six propositions are equivalent. Before we engage in the proof
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

(* this is the reverse of and_to_or *)
Lemma L3 : forall P Q:Prop, P\/Q->~(~P/\~Q).
Proof.
  intros P Q H; intro H'; elim H'; intros Hnp Hnq. elim H.
  intro Hp; apply Hnp; exact Hp.
  intro Hq; apply Hnq; exact Hq.
Qed.

(* this is the reverse of imp_to_or *)
Lemma L4 : forall P Q: Prop, (~P\/Q)->(P->Q).
Proof.
  intros P Q H Hp. elim H. intro Hnp.
  apply False_ind. apply Hnp; exact Hp.
  intro Hq; exact Hq.
Qed.

Lemma L5 : forall (A:Type) (P: A->Prop),
  (forall x:A, P x) -> ~(exists x:A, ~P x).
Proof. 
  intros A P H H'. elim H'. intros a Ha. apply Ha. apply H. 
Qed.


Theorem peirce_to_classic : peirce->classic.
Proof.
  unfold peirce. unfold classic.
  intro H. intro P. intro H'.
  cut ((P->False)->P). intro H0.
  apply H with (Q:=False). exact H0.
  intro H1. apply False_ind. apply H'. exact H1.
Qed.

Theorem classic_to_lem : classic->lem.
Proof.
  unfold classic. unfold lem.
  intro H. intro P. apply H with (P:=P\/~P).
  intro H'. cut (~~P). intro H0. cut (~P).
  intro Hp. apply H0. exact Hp. intro Hp. apply H'.
  left; exact Hp. intro H1. apply H'. right; exact H1.
Qed.

Theorem lem_to_and_or : lem->and_to_or.
Proof.
  unfold lem. unfold and_to_or.
  intro ExM. intros P Q. intro H. cut ((P\/Q) \/~(P\/Q)).
  intro H0. elim H0. intro H1. exact H1. intro H2.
  apply False_ind. apply H. split. intro Hp. apply H2.
  left; exact Hp. intro Hq. apply H2. right; exact Hq. apply ExM.
Qed.


Theorem and_or_to_imp_or : and_to_or->imp_to_or.
Proof.
  unfold and_to_or. unfold imp_to_or.
  intro H. intros P Q. intro Hpq. cut(P\/~P). intro H1.
  elim H1. intro Hp. right. apply Hpq; exact Hp.
  intro H2. left; exact H2. apply H. intro H3. elim H3.
  intros H4 H5. apply H5; exact H4.
Qed.

Theorem imp_or_to_ex_all : imp_to_or->ex_to_all.
Proof.
  unfold imp_to_or, ex_to_all. intros H A P H' a.
  cut(~P a\/P a). intro Hex. elim Hex. intro Hna.
  apply False_ind. apply H'. exists a. exact Hna.
  trivial. apply H. trivial.
Qed.


(* rather than showing ex_to_all->peirce to close the loop,
we go for a more natural result, ex_to_all->classic *)
Theorem ex_all_to_classic :  ex_to_all->classic.
Proof.
  unfold ex_to_all, classic. intros A P H.
  pose (Q := (fun (x:Prop) => P)).
  cut(forall x:Prop, Q x). intro H'.
  cut(Q False). intro H''. exact H''. apply H'. apply A.
  intro H'. apply H. elim H'. intros a Ha. exact Ha.
Qed.
 

(* we now close the loop *)
Theorem imp_or_to_peirce : imp_to_or->peirce.
Proof.
  unfold imp_to_or. unfold peirce. intro H. intros P Q.
  intro H'. cut (~P\/P). intro H0. elim H0. intro H1.
  apply H'. intro Hp. apply False_ind. apply H1. exact Hp.
  intro Hp; exact Hp. apply H. intro Hp; exact Hp.
Qed.

