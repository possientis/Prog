(* some useful bindings *)
Definition peirce                 := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic                := forall P:Prop, ~~P -> P.
Definition lem                    := forall P:Prop, P \/ ~P.
Definition and_to_or              := forall P Q:Prop, ~(~P /\ ~Q) -> P \/ Q.
Definition imp_to_or              := forall P Q:Prop, (P -> Q) -> (~P \/ Q).
Definition ex_to_all              := forall (A:Type) (P: A -> Prop), 
    ~(exists x:A, ~P x) -> (forall x:A, P x).


(* discriminate tactic*)
Lemma true_neq_false1 : true <> false.
Proof. intros H. discriminate. Qed.

Definition toProp (b:bool) : Prop := if b then True else False.

(* change tactic *)
Lemma true_neq_false2 : true <> false.
Proof. intros H. change (toProp  false). rewrite <- H. simpl. exact I. Qed.

(* congruence tactic *)
Lemma true_neq_false3 : true <> false.
Proof. intros H. congruence. Qed.

(* injection tactic *)
Lemma S_inj1 : forall (n m:nat), S n = S m -> n = m.
Proof. intros n m H. injection H. intros. assumption. Qed.

(* change tactic *)
Lemma S_inj2 : forall (n m:nat), S n = S m -> n = m.
Proof. 
    intros n m H. change (pred (S n) = pred (S m)). 
    rewrite H. reflexivity. 
Qed.

(* apply tactic *)
Lemma obvious1 : True.
Proof. apply I. Qed.

(* constructor tactic *)
Lemma obvious2 : True.
Proof. constructor. Qed.

(* destruct tactic *)
Lemma False_imp1: False -> 2 + 2 = 5.
Proof. intros H. destruct H. Qed.

(* exfalso tactic *)
Lemma False_imp2: False -> 2 + 2 = 5.
Proof. intros H. exfalso. assumption. Qed.

(* discriminate tactic *)
Lemma not1 : ~(2 + 2 = 5).
Proof. intros H. discriminate H. Qed.

Fixpoint even (n:nat) : bool :=
    match n with
    | 0     => true
    | S p   => negb (even p)
    end.

(* change tactic *)
Lemma not2 : ~(2 + 2 = 5).
Proof. intros H. change (toProp (even 5)). rewrite <- H. simpl. apply I. Qed.

(* split tactic *)
Lemma and_comm1 : forall (A B:Prop), A /\ B -> B /\ A.
Proof. intros A B [H1 H2]. split; assumption. Qed.

(* left and right tactics *)
Lemma or_comm1 : forall (A B:Prop), A \/ B -> B \/ A.
Proof. 
    intros A B [H1|H2].
    - right. assumption.
    - left . assumption.
Qed. 

(* tauto tactic *)
Lemma and_comm2 : forall (A B:Prop), A /\ B -> B /\ A.
Proof. tauto. Qed. 


(* tauto tactic *)
Lemma or_comm2 : forall (A B:Prop), A \/ B -> B \/ A.
Proof. tauto. Qed. 

(* exists tactic *)
Lemma exist1 : exists (n:nat), n + 3 = 5.
Proof. exists 2. reflexivity. Qed.

(* firstorder tactic *)
Lemma firstorder1 : forall (A:Type) (P: A->Prop),
  (forall x:A, P x) -> ~(exists x:A, ~P x).
Proof.  firstorder. Qed.

(* intuition tactic *)
Lemma intuition1 : peirce -> classic.
Proof.
  unfold peirce. unfold classic. intuition.
  apply H with False. intros H1. exfalso. apply H0. assumption.
Qed.

(* firstorder tactic *)
Lemma firstorder2 : peirce -> classic.
Proof.
  unfold peirce. unfold classic. firstorder.
  apply H with False. intros H1. exfalso. apply H0. assumption.
Qed.

(* cut tactic *)
Lemma cut1: 1 + 1 = 2.
Proof. 
    cut (2 + 2 = 4).
    - intros E. reflexivity.
    - reflexivity. 
Qed.

(* assert tactic *)
Lemma assert1: 1 + 1 = 2.
Proof.
    assert (2 + 2 = 4) as E.
    - reflexivity.
    - reflexivity.
Qed.

(* remember tactic *)
Lemma remember1 : 1 + 1 = 2.
    remember 1 as x eqn:E.
    rewrite E. reflexivity.
Qed.

