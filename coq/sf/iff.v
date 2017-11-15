Module MYIFF.

Definition iff (P Q:Prop) : Prop := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) (* : type_scope *).

End MYIFF.


Theorem iff_sym : forall (P Q:Prop),
    (P <-> Q) -> (Q <-> P).
Proof. intros P Q [H1 H2]. split. exact H2. exact H1. Qed.


Lemma not_true_iff_false : forall (b:bool),
    b <> true <-> b = false.
Proof.
    intros b. destruct b. 
    - split.
        + intros H. exfalso. apply H. reflexivity.
        + intros H. inversion H.
    - split.
        + intros. reflexivity.
        + intros H1 H2. inversion H2.
Qed.


Theorem iff_refl : forall (P:Prop),
    P <-> P.
Proof. 
    intros P. split.
    - intros H. exact H.
    - intros H. exact H.
Qed.

Theorem iff_trans : forall (P Q R:Prop),
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros P Q R [Hpq Hqp] [Hqr Hrq]. split.
    - intro Hp. apply Hqr. apply Hpq. exact Hp.
    - intro Hr. apply Hqp. apply Hrq. exact Hr.
Qed.


Theorem or_distributes_over_and : forall (P Q R:Prop),
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros P Q R. split. 
    - intros [Hp|[Hq Hr]].
        + split. { left. exact Hp. } { left. exact Hp. }
        + split. { right. exact Hq. } { right. exact Hr. }
    - intros [[H1|Hq] [H2|Hr]].
        + left. exact H1.
        + left. exact H1.
        + left. exact H2. 
        + right. split. { exact Hq. } { exact Hr. }
Qed.


