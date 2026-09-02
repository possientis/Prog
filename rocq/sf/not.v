Theorem ex_falso_quodlibet : forall (P:Prop),
    False -> P.
Proof. intros P H. destruct H. Qed. (* or inversion H *)

Notation "¬ P" := (~ P) (at level 40).

Theorem not_implies_our_not : forall (P:Prop),
    ¬ P -> (forall (Q:Prop), P -> Q).
Proof. intros P H Q H'. apply H in H'. inversion H'. Qed.


Theorem zero_not_one : ¬ (0 = 1).
Proof. intros H. inversion H. Qed.


Theorem not_False : ¬ False.
Proof. intros H. exact H. Qed.


Theorem contradiction_implies_anything : forall (P Q:Prop),
    (P /\ ¬P) -> Q.
Proof. intros P Q [H1 H2]. apply H2 in H1. inversion H1. Qed.

Theorem double_neg : forall (P:Prop),
    P -> ¬(¬P).
Proof. intros P H H'. apply H' in H. inversion H. Qed.

Theorem contrapositive : forall (P Q: Prop), 
    (P -> Q) -> (¬Q -> ¬P).
Proof.
    intros P Q Hpq Hnq Hp. apply Hpq in Hp. apply Hnq in Hp. exact Hp.
Qed.


Theorem not_both_true_and_false : forall (P:Prop),
    ¬(P /\ ¬P).
Proof. intros P [H1 H2]. apply H2 in H1. exact H1. Qed.


Theorem not_true_is_false : forall (b:bool),
    b <> true -> b = false.
Proof.
    intros b H. destruct b.
    - exfalso. apply H. reflexivity.
    - reflexivity.
Qed.

Lemma True_is_true : True.
Proof. exact I. Qed.

