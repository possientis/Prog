(*
Inductive or(P Q:Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q
.

Notation "P \/ Q" := (or P Q).
*)

(*
Lemma or_introl : forall (P Q:Prop),
    P -> P \/ Q.
Proof. intros P Q H. left. exact H. Qed.

Lemma or_intror : forall (P Q:Prop),
    Q -> P \/ Q.
Proof. intros P Q H. right. exact H. Qed.
*)

Lemma or_comm : forall (P Q:Prop),
    P \/ Q -> Q \/ P.
Proof.
    intros P Q [H1|H2].
    - right. exact H1.
    - left. exact H2.
Qed.


Lemma or_assoc : forall (P Q R:Prop),
    P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
    intros P Q R. split.
    - intros [Hp | [Hq | Hr]].
        + left. left. exact Hp.
        + left. right. exact Hq.
        + right. exact Hr.
    - intros [[Hp|Hq]|Hr]. 
        + left. exact Hp.
        + right. left. exact Hq.
        + right. right. exact Hr.
Qed.


