Require Import Peano_dec.

(* Definition works for 'strict-like' relations                                 *)
Inductive Accessible (a:Type)(r:a -> a -> Prop) : a -> Prop := 
| Acc : forall (x:a), (forall (y:a), r y x -> Accessible a r y) -> 
    Accessible a r x
.

Arguments Accessible {a}.

Definition WellFounded (a:Type) (r:a -> a -> Prop) :=
    forall (x:a), Accessible r x.

Arguments WellFounded {a}.

Lemma L1 : forall (a:Type) (r:a -> a -> Prop) (x y:a),
    r x y -> Accessible r y  -> Accessible r x.
Proof.
    intros a r x y R Ay. destruct Ay as [y H].
    apply H. assumption.
Qed.


Lemma L2 : WellFounded lt.
Proof.
    unfold WellFounded. intros n. induction n as [|n IH].
    - constructor. intros n H. inversion H.
    - constructor. intros m H. destruct (eq_nat_dec n m) as [H'|H'].
        + subst. assumption.
        + apply L1 with n.
            { unfold lt in H.

Show.


