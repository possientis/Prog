(*
Inductive and (P Q:Prop) : Prop :=
| conj: P -> Q -> and P Q
.

Arguments conj {P} {Q} _ _.

Notation "P /\ Q" := (conj P Q).
*)

Theorem and_comm : forall (P Q:Prop),
    P /\ Q -> Q /\ P.
Proof.
    intros P Q [H1 H2]. split.
    - exact H2.
    - exact H1.
Qed.

Theorem and_assoc : forall (P Q R:Prop),
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
    intros P Q R [H1 [H2 H3]]. split.
    - split.
        + exact H1.
        + exact H2.
    - exact H3.
Qed.

