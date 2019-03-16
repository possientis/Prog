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

