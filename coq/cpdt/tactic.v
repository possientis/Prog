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






