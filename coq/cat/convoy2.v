Definition bool_func (a:Type) : Type := a -> a -> bool.

Definition proof_func (a:Type) : Type := forall (x y:a), option (x = y).


Definition bool_correct (a:Type) (f: bool_func a) : Prop :=
    forall (x y:a), x = y <-> f x y = true.

Definition proof_correct (a:Type) (f: proof_func a) : Prop :=
    forall (x y:a), x = y <-> f x y <> None.

Arguments bool_correct {a} _.
Arguments proof_correct {a} _.
    
Definition has_bool (a:Type) : Prop := exists (f: bool_func a), bool_correct f. 

Definition has_proof (a:Type) : Prop := exists (f: proof_func a), proof_correct f.

Definition to_bool_func (a:Type) (f: proof_func a) (x y:a) : bool :=
    match f x y with
    | Some _        => true
    | None          => false
    end.

Lemma has_proof_has_bool : forall (a:Type), has_proof a -> has_bool a.
Proof.
    intros a. unfold has_proof, has_bool. intros H. destruct H as [f H].
    exists (to_bool_func a f). split.
    - intros H'. destruct (f x y) eqn:H0.
        + unfold to_bool_func. rewrite H0. reflexivity.
        + apply H in H'. exfalso. apply H'. exact H0.
    - intros H'. destruct (f x y) eqn:H0. 
        + exact e.
        + unfold to_bool_func in H'. rewrite H0 in H'. inversion H'.
Qed.


