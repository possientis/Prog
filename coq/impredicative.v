Set Implicit Arguments.

Definition myTrue : Prop := forall P:Prop, P->P. (* impredicative definition : refers to itself *)

Definition myFalse: Prop := forall P:Prop, P.    (* impredicative definition *)
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


Definition myAnd (P Q:Prop) :=
  forall R:Prop, (P->Q->R)->R.

Definition myOr (P Q:Prop) :=
  forall R:Prop, (P->R)->(Q->R)->R.

Definition myEx (A:Type)(P: A->Prop) :=
  forall R:Prop, (forall x:A, P x -> R)->R.

Lemma L2 : forall P Q:Prop, myAnd P Q -> P.
Proof.
  intros P Q H. unfold myAnd in H. apply H. intros p q. exact p.
Qed.

Lemma L3 : forall P Q:Prop, myAnd P Q -> Q.
Proof.
  intros P Q H. unfold myAnd in H. apply H. intros p q. exact q.
Qed.

Check and_ind. (* forall A B P : Prop, (A -> B -> P) -> A /\ B -> P *)
Lemma myAnd_ind : forall P Q R : Prop, (P->Q->R)-> myAnd P Q -> R.
Proof.
  intros P Q R H and. unfold myAnd in and. apply and. exact H.
Qed.

Lemma L4 : forall P Q: Prop, P-> myOr P Q.
Proof.
  intros P Q p. unfold myOr. intros R Hp Hq. apply Hp. exact p.
Qed.


Lemma L5 : forall P Q: Prop, Q-> myOr P Q.
Proof.
  intros P Q q. unfold myOr. intros R Hp Hq. apply Hq. exact q.
Qed.

Check or_ind. (* forall A B P : Prop, (A -> P) -> (B -> P) -> A \/ B -> P *)
Lemma myOr_ind : forall P Q R: Prop, (P->R) -> (Q->R) -> myOr P Q -> R.
Proof.
  intros P Q R Hp Hq H. apply H. exact Hp. exact Hq. 
Qed.

Lemma L6 : forall P:Prop, myOr P myFalse -> P.
Proof.
  intros P H. unfold myOr in H. apply H. intro p. exact p. apply myFalse_ind.
Qed.

Lemma L7 : forall P Q:Prop, myOr P Q -> myOr Q P.
Proof.
  intros P Q H. unfold myOr in H. apply H. 
  apply L5 with (Q:=P)(P:=Q). apply L4 with (Q:=P)(P:=Q).
Qed.

Check ex_ind. (* forall (A : Type) (P : A -> Prop) (P0 : Prop),
                (forall x : A, P x -> P0) -> (exists x, P x) -> P0 *)

Check ex_intro. (* forall (A : Type) (P : A -> Prop) (x : A), P x -> exists x, P x *) 

Lemma myEX_intro : forall (A:Type)(P:A->Prop)(a:A), P a -> myEx P.
Proof.
  intros A P a H. unfold myEx. intros R All. apply All with (x:=a). exact H.
Qed.

Lemma L8 : forall (A:Type)(P:A->Prop),
  myNot (myEx P) -> forall a:A, myNot (P a).
Proof.
  intros A P H a. unfold myNot. unfold myNot in H. intro Pa. apply H. unfold myEx.
  intros R all. apply all with (x:=a). exact Pa.
Qed.

Definition myLe (n p:nat) :=
  forall P:nat->Prop, P n -> (forall q:nat, P q -> P (S q)) -> P p.

Check le_n. (* forall n : nat, n <= n *)

Lemma myLe_n : forall n:nat, myLe n n.
Proof.
  unfold myLe. intros n P H0 H1. exact H0.
Qed.

Check le_S. (* forall n m : nat, n <= m -> n <= S m *)

Lemma myLe_S : forall n m:nat, myLe n m -> myLe n (S m).
Proof.
  intros n m H. unfold myLe in H. apply H. unfold myLe.
  intros P Pn Stable. apply Stable. exact Pn. intros q H0.
  unfold myLe. intros P Pn Stable. unfold myLe in H0. apply Stable.
  apply H0. exact Pn. exact Stable.
Qed.

Lemma myLe_le : forall n m:nat, myLe n m -> n <=  m.
Proof.
  intros n m H. unfold myLe in H. apply H. apply le_n.
  intros q H0. apply le_S. exact H0.
Qed.

Check nat_ind. (* forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n *)

Lemma le_myLe : forall n m: nat, n <= m -> myLe n m.
Abort.
