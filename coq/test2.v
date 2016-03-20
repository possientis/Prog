Set Implicit Arguments.
 

Definition classic := forall P:Prop, ~~P -> P.
Definition classic_reverse := forall P:Prop,
  P -> ~~P.

Lemma L1: classic_reverse.
Proof.
  unfold classic_reverse.
  intro P.
  unfold not at 1.
  unfold not.
  intro Hp.
  intro Hnp.
  apply Hnp.
  exact Hp.
Qed.

Definition lem := forall P:Prop, P \/ ~P.

Theorem classic_to_lem: classic -> lem.
Proof.
  unfold classic, lem.
  intro classic.
  intro P.
  apply classic.
  unfold not at 1.
  intro H.
  unfold not in H at 1.
  cut (~P).
  intro Hnp.
  cut (~P->False).
  intro H1.
  apply H1.
  exact Hnp.
  intro H2.
  apply H.
  right. 
  exact H2.
 
  unfold not.
  intro Hp.
  apply H.
  left.
  exact Hp.
Qed. 

Theorem lem_to_classic: lem -> classic.
Proof.
  unfold lem, classic.
  intro lem.
  intro P.
  intro Hnnp.
  unfold not at 1 in Hnnp.
  cut (P \/ ~P).
  intro H. 
  elim H. 
  intro Hp.
  exact Hp. 
  intro H1.
  apply False_ind. 
  apply Hnnp.
  exact H1. 
  apply lem. 
Qed.

Definition peirce := forall P Q:Prop, ((P->Q)->P)->P.

Theorem implication_is_transitive: forall A B C:Prop, 
  (A->B)->(B->C)->(A->C).

Proof.
  intros A B C.
  intro Hab.
  intro Hbc. 
  intro Ha. 
  apply Hbc.
  apply Hab.
  exact Ha. 
Qed. 

Theorem equivalence_is_transitive: forall A B C:Prop,
  (A<->B)->(B<->C)->(A<->C).
Proof.

  intros A B C. 
  intro Hab. 
  intro Hbc. 
  split. 
  apply implication_is_transitive with (B:=B).
  elim Hab. 
  intros H0 H1. 
  exact H0. 
  elim Hbc.
  intros H2 H3.
  exact H2.
  apply implication_is_transitive with (B:=B).
  elim Hbc.
  intros H4 H5. 
  exact H5. 
  elim Hab.
  intros H6 H7.
  exact H7. 
Qed.



