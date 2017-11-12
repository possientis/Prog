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


