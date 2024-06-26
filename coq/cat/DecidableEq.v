Definition bool_func (a:Type) : Type := a -> a -> bool.

Definition proof_func (a:Type) : Type := forall (x y:a), option (x = y).

Definition lem_func (a:Type) : Type := forall (x y:a), {x = y} + {x <> y}. 

Definition bool_correct (a:Type) (f:bool_func a) : Prop :=
    forall (x y:a), x = y <-> f x y = true.

Definition proof_correct (a:Type) (f:proof_func a) : Prop :=
    forall (x y:a), x = y <-> f x y <> None.

Definition lem_correct (a:Type) (f:lem_func a) : Prop :=
    forall (x y:a), x = y <-> exists p, f x y = left p.

Arguments bool_correct {a} _.
Arguments proof_correct {a} _.
Arguments lem_correct {a} _.

Lemma lem_func_always_correct: forall (a:Type) (f:lem_func a), lem_correct f.
Proof.
    intros a f. unfold lem_correct. intros x y. split. 
    - intros H. destruct (f x y) as [e|e] eqn:H'.
        + exists e. reflexivity.
        + exfalso. apply e. exact H.
    - intros [p H]. exact p.
Qed.

Definition has_bool (a:Type) : Prop := exists (f:bool_func a), bool_correct f. 

Definition has_proof (a:Type) : Prop := exists (f:proof_func a), proof_correct f.

Definition has_lem (a:Type) : Prop := exists (f:lem_func a), True. 

Definition proof_to_bool (a:Type) (f:proof_func a) (x y:a) : bool :=
    match f x y with
    | Some _        => true
    | None          => false
    end.

Definition lem_to_bool (a:Type) (f:lem_func a)(x y:a) : bool :=
    match f x y with
    | left _        => true
    | right _       => false
    end.


Lemma has_proof_has_bool : forall (a:Type), has_proof a -> has_bool a.
Proof.
    intros a. unfold has_proof, has_bool. intros [f H]. 
    exists (proof_to_bool a f). split.
    - intros H'. destruct (f x y) eqn:H0.
        + unfold proof_to_bool. rewrite H0. reflexivity.
        + apply H in H'. exfalso. apply H'. exact H0.
    - intros H'. destruct (f x y) eqn:H0. 
        + exact e.
        + unfold proof_to_bool in H'. rewrite H0 in H'. inversion H'.
Qed.

Lemma has_lem_has_bool : forall (a:Type), has_lem a -> has_bool a.
Proof.
    intros a. unfold has_lem, has_bool. intros [f H]. 
    exists (lem_to_bool a f). split.
    - intros H'. destruct (f x y) eqn:H0. 
        + unfold lem_to_bool. rewrite H0. reflexivity.
        + assert (exists p, f x y = left p) as H1.
            { apply (lem_func_always_correct a f x y). exact H'. }
          destruct H1 as [p H1]. rewrite H1 in H0. inversion H0. 
    - intros H'. destruct (f x y) eqn:H0.
        + exact e.
        + unfold lem_to_bool in H'. rewrite H0 in H'. inversion H'.
Qed.


Definition to_eq_proof (a:Type) (f:bool_func a) (x y:a) (p:f x y = true) : 
    bool_correct f -> x = y.
Proof. intro H. apply H. exact p. Qed.

Arguments to_eq_proof {a} {f} {x} {y} _ _.

Definition to_neq_proof (a:Type) (f:bool_func a) (x y:a) (p:f x y = false) :
    bool_correct f -> x <> y.
Proof. intros H E. apply H in E. rewrite p in E. inversion E. Qed.

Arguments to_neq_proof {a} {f} {x} {y} _ _ _.

Definition to_proof_func (a:Type) (f:bool_func a) (p:bool_correct f) (x y:a) :
    option (x = y) :=
    match f x y as b return f x y = b -> option (x = y) with
    | true      => fun q    => Some (to_eq_proof q p)
    | false     => fun _    => None
    end (eq_refl (f x y)).

Arguments to_proof_func {a} {f} _ _ _.

Definition to_lem_func (a:Type) (f:bool_func a) (p:bool_correct f) (x y:a) :
    {x = y} + {x <> y} :=
    match f x y as b return  f x y = b -> {x = y} + {x <> y} with
    | true      => fun q    => left  (to_eq_proof q p)
    | false     => fun q    => right (to_neq_proof q p)
    end (eq_refl (f x y)).





Arguments to_lem_func {a} {f} _ _ _.

Definition to_proof_gen (a:Type) (f:bool_func a) (p:bool_correct f)
    (x y:a) (b:bool) (q:f x y = b) : option (x = y) :=
    match b as b1 return f x y = b1 -> option (x = y) with
    | true      => fun r    => Some (to_eq_proof r p)
    | false     => fun _    => None
    end q.

Arguments to_proof_gen {a} {f} _ _ _ _ _.

(* so far so good *)
Example check1 : forall (a:Type) (f:bool_func a) (p:bool_correct f) (x y:a),
    to_proof_func p x y = to_proof_gen p x y (f x y) (eq_refl (f x y)).
Proof. reflexivity. Qed. 

Lemma to_proof_gen_correct : forall (a:Type) (f:bool_func a) (p:bool_correct f),
    forall (x:a) (b:bool) (q:f x x = b), to_proof_gen p x x b q <> None.
Proof.
    intros a f p x b q H. destruct b eqn:H'.
    - inversion H.
    - clear H. assert (f x x = true). { apply p. reflexivity. }
        rewrite q in H. inversion H.
Qed.

Lemma to_proof_gen_correct' : forall (a:Type) (f:bool_func a) (p: bool_correct f),
    forall (x y:a) (b:bool) (q:f x y = b), to_proof_gen p x y b q <> None -> x = y.
Proof.
    intros a f p x y b q H. destruct b eqn:H'.
    - apply p. exact q.
    - unfold to_proof_gen in H. exfalso. apply H. reflexivity.
Qed.

Lemma to_proof_func_correct : forall (a:Type) (f:bool_func a) (p:bool_correct f),
    forall (x y:a), x = y <-> to_proof_func p x y <> None.
Proof.
    intros a f p x y. split.
    - intros H. rewrite H. apply to_proof_gen_correct.
    - intros H. apply (to_proof_gen_correct' a f p x y (f x y) (eq_refl (f x y))).
        exact H.
Qed.

Lemma has_bool_has_proof : forall (a:Type), has_bool a -> has_proof a.
Proof.
    intros a. unfold has_bool, has_proof. intros [f H].
    exists (to_proof_func H).
    unfold proof_correct. apply to_proof_func_correct.
Qed.

Lemma has_bool_has_lem : forall (a:Type), has_bool a -> has_lem a.
Proof.
    intros a. unfold has_bool, has_proof. intros [f H].
    exists (to_lem_func H). apply I.
Qed.



Theorem bool_proof_iff : forall (a:Type), has_bool a <-> has_proof a.
Proof.
    intros a. split.
    - apply has_bool_has_proof.
    - apply has_proof_has_bool.
Qed.

Theorem bool_lem_iff : forall (a:Type), has_bool a <-> has_lem a.
Proof.
    intros a. split.
    - apply has_bool_has_lem.
    - apply has_lem_has_bool.
Qed.

Theorem proof_lem_iff : forall (a:Type), has_proof a <-> has_lem a.
Proof.
    intros a. split.
    - intros H. apply has_bool_has_lem. apply has_proof_has_bool. exact H.
    - intros H. apply has_bool_has_proof. apply has_lem_has_bool. exact H.
Qed.


    
(* If we attempt to use a 'Prop' version of HasDecidableEq *) 
Definition HasDecidableEq' (a:Type) : Prop :=
    forall (x y:a), x = y \/ x <> y.

(* Then we cannot perform a case analysis:
Incorrect elimination of "p x y" in the inductive type "or":
the return type has sort "Set" while it should be "Prop".
Elimination of an inductive object of sort Prop
is not allowed on a predicate in sort Set
because proofs can be eliminated only to build proofs.

Definition to_func' (a:Type) (p:HasDecidableEq' a) (x y:a) : bool :=
    match p x y with
    | or_introl _   => true
    | or_intror _   => false
    end.
*)






