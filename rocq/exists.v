Theorem ex_imp_ex : 
  forall (A:Type)(P Q: A->Prop), (ex P)->(forall x:A, P x -> Q x)->(ex Q).
Proof.
(*
  firstorder.
*)
  intros A P Q H Hpq.
  elim H.
  intro a. intro Ha.
  exists a.
  apply Hpq.
  exact Ha.
Qed.


Section test.
  Variable A : Type.
  Variables P Q: A->Prop.

Lemma L1 : (exists x:A, P x \/ Q x) -> (ex P)\/(ex Q).
Proof.
(*
  firstorder.
*)
  intro H. elim H. intros a Ha. elim Ha.
  intro Pa. left. exists a. exact Pa. 
  intro Qa. right. exists a. exact Qa.
Qed.

Lemma L2 : (ex P)\/(ex Q) -> (exists x:A, P x \/ Q x).
Proof.
(*
  firstorder.
*)
  intro H. elim H.
  intro Hp. elim Hp. intros a Pa. exists a. left. exact Pa.
  intro Hq. elim Hq. intros a Qa. exists a. right. exact Qa.
Qed.

Lemma L3 : (exists x:A, (forall R : A->Prop, R x)) -> 2 = 3. 
Proof.
  intro H.
  apply False_ind.
  elim H. intros a Ha. 
  pose (R := (fun (x:A) => False)). (* using the 'pose' tactic *)
  apply Ha with (R:=R).
Qed.

Lemma L4 : (forall x:A, P x) -> ~(exists x:A, ~ P x).
Proof.
(*
  firstorder.
*)
  intro H.
  intro H'. elim H'. intros a Ha.
  apply Ha. apply H.
Qed.


