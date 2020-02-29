Definition L1 : forall (A:Prop), ~~(A \/ ~A).
Proof.
    intros A H.
    assert (~A)  as H1. { intros H'. apply H. left.  assumption. }
    assert (~~A) as H2. { intros H'. apply H. right. assumption. }
    apply H2. assumption.
Qed.

Definition L2 : forall (A:Prop), ~~(A \/ ~A) :=
    fun (A:Prop) =>
        fun (f: ~(A \/ ~A)) =>
            (fun (x:~A) => f (or_intror x)) (fun (x:A) => f (or_introl x)).
