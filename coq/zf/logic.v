(* No axiom is being used in this module *)

(* This is the reverse of Peirce law which is not very interesting *)
Proposition peirce_reverse : forall P Q: Prop, P->(P->Q)->P.
Proof.
  intros P Q Hp; intro Hpq; exact Hp.
Qed.

Proposition P_non_P : forall P:Prop, P->~~P.
Proof.
  intros P Hp; intro H; apply H; exact Hp.
Qed.

Proposition or_not_and_not : forall P Q:Prop, P\/Q->~(~P/\~Q).
Proof.
  intros P Q H; intro H'; elim H'; intros Hnp Hnq. elim H.
  intro Hp; apply Hnp; exact Hp.
  intro Hq; apply Hnq; exact Hq.
Qed.


Proposition not_P_or_imp : forall P Q: Prop, (~P\/Q)->(P->Q).
Proof.
  intros P Q H Hp. elim H. intro Hnp.
  apply False_ind. apply Hnp; exact Hp.
  intro Hq; exact Hq.
Qed.

Proposition forall_not_exists : forall (A:Type) (P: A->Prop),
  (forall x:A, P x) -> ~(exists x:A, ~P x).
Proof. 
  intros A P H H'. elim H'. intros a Ha. apply Ha. apply H. 
Qed.


 

