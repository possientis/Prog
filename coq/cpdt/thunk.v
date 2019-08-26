CoInductive Thunk (a:Type) : Type :=
| Answer : a -> Thunk a
| Think  : Thunk a -> Thunk a
.

Arguments Answer {a}.
Arguments Think {a}.

Definition pure (a:Type) (x:a) : Thunk a := Answer x.

Arguments pure {a}.

CoFixpoint bind (a b:Type) (k:Thunk a) (f:a -> Thunk b) : Thunk b :=
    match k with
    | Answer x  => f x
    | Think k' => Think (bind a b k' f)
    end.

Arguments bind {a} {b}.


Notation "k >>= f" := (bind k f) (at level 50, left associativity).

CoInductive thunk_eq (a:Type) : Thunk a -> Thunk a -> Prop :=
| Answer_eq : forall (x y:a), x = y -> thunk_eq a (Answer x) (Answer y)
| Think_eq  : forall (t1 t2:Thunk a), 
    thunk_eq a t1 t2 -> thunk_eq a (Think t1) (Think t2)
.

Arguments thunk_eq {a}.

(* was useful when dealing with stream                                          *)
Definition frob (a:Type) (t:Thunk a) : Thunk a :=
    match t with
    | Answer x  => Answer x
    | Think t'  => Think t'
    end.

Arguments frob {a}.

Lemma frob_same : forall (a:Type) (t:Thunk a), t = frob t.
Proof. intros a. destruct t as [x|t]; reflexivity. Qed.

Lemma thunk_eq_coind : forall (a:Type) (R:Thunk a -> Thunk a -> Prop),
    (forall (x y:a), R (Answer x) (Answer y) -> x = y)           ->
    (forall (t1 t2:Thunk a), R (Think t1) (Think t2) -> R t1 t2) ->
    (forall (x:a)(t2:Thunk a), ~R (Answer x) (Think t2))         ->
    (forall (y:a)(t1:Thunk a), ~R (Think t1) (Answer y))         ->
    (forall (t1 t2:Thunk a), R t1 t2 -> thunk_eq t1 t2).
Proof.
    intros a R H1 H2 H3 H4. cofix. intros [x|t1] [y|t2] H.
    - apply H1 in H. rewrite H. constructor. reflexivity.
    - exfalso. apply (H3 x t2). assumption.
    - exfalso. apply (H4 y t1). assumption.
    - apply H2 in H. constructor. apply thunk_eq_coind. assumption.
Qed.

Arguments thunk_eq_coind {a}.

(* direct proof using cofix tactic                                              *)
Lemma thunk_eq_refl : forall (a:Type) (t:Thunk a), thunk_eq t t.
Proof.
    intros a. cofix. intros [x|t].
    - constructor. reflexivity.
    - constructor. apply thunk_eq_refl.
Qed.

(* proof using coinduction principle                                            *)
Lemma thunk_eq_refl' : forall (a:Type) (t:Thunk a), thunk_eq t t.
Proof.
    intros a t. apply (thunk_eq_coind (fun x y => x = y)).
    - intros x y H.   inversion H. reflexivity.
    - intros t1 t2 H. inversion H. reflexivity.
    - intros x t2 H.  inversion H.
    - intros y t1 H.  inversion H.
    - reflexivity.
Qed.

(* direct proof using cofix tactic                                              *)
Lemma thunk_eq_sym : forall (a:Type) (t1 t2:Thunk a),
    thunk_eq t1 t2 -> thunk_eq t2 t1.
Proof.
    intros a. cofix. intros t1 t2 H. destruct H as [x y|t1 t2].
    - constructor. symmetry. assumption.
    - constructor. apply thunk_eq_sym. assumption.
Qed.
(*
(* proof using coinduction principle                                            *)
Lemma thunk_eq_sym' : forall (a:Type) (t1 t2:Thunk a),
    thunk_eq t1 t2 -> thunk_eq t2 t1.
Proof.
    intros a t1 t2 H. apply (thunk_eq_coind (fun x y => thunk_eq y x)).
    - clear t1 t2 H. intros x y H.

Show.
*)
(*
      remember (Answer x) as t1 eqn:E1.
      remember (Answer y) as t2 eqn:E2.
      intros H. revert E1 E2. destruct H.
      + intros H1 H2. inversion H1. inversion H2. subst. reflexivity.
      + intros H1 H2. inversion H1. 
    - clear t1 t2 H. intros t1 t2.
      remember (Think t1) as t1' eqn:E1.
      remember (Think t2) as t2' eqn:E2.
      intros H. revert E1 E2. destruct H.
      + intros H1 H2. inversion H1.
      + intros H1 H2. inversion H1. inversion H2. subst. assumption.
    - clear t1 t2 H. intros x t2.
      remember (Answer x) as t1' eqn:E1.
      remember (Think t2) as t2' eqn:E2.
      intros H. revert E1 E2. destruct H.
      + intros H1 H2. inversion H2.
      + intros H1 H2. inversion H1.
    - clear t1 t2 H. intros y t1.
      remember (Think t1) as t1' eqn:E1.
      remember (Answer y) as t2' eqn:E2.
      intros H. revert E1 E2. destruct H.
      + intros H1 H2. inversion H1.
      + intros H1 H2. inversion H2.
    - assumption.
Qed.


(* direct proof using cofix tactic                                              *)
Lemma thunk_eq_trans : forall (a:Type) (t1 t2 t3:Thunk a),
    thunk_eq t1 t2 -> thunk_eq t2 t3 -> thunk_eq t1 t3.
Proof.
    intros a. cofix. intros t1 t2 t3 H. revert t3. destruct H.
    - subst. intros t3 H. assumption.
    - intros t3. remember (Think t2) as t2' eqn:E. 
      intros H'. revert E. destruct H'.
        + intros H1. inversion H1.
        + intros H1. inversion H1. subst. constructor.
          apply thunk_eq_trans with t2; assumption.
Qed.


(* proof using coinduction principle                                            *)
Lemma thunk_eq_trans' : forall (a:Type) (t1 t2 t3:Thunk a),
    thunk_eq t1 t2 -> thunk_eq t2 t3 -> thunk_eq t1 t3.
Proof.
    intros a t1 t2 t3 H1 H2.
    apply (thunk_eq_coind (fun x z => exists y, thunk_eq x y /\ thunk_eq y z)).
    - clear H1 H2 t1 t2 t3. intros x y [t [H1 H2]].
      revert H2. remember (Answer x) as t1 eqn:E1. revert E1. destruct H1.
      + subst. intros H. inversion H. subst. clear H. intros H.
        inversion H. assumption.
      + intros H. inversion H.
    - clear H1 H2 t1 t2 t3.
      intros t1 t2 [t [H1 H2]].
      remember (Think t1) as t1' eqn:E1.
      remember (Think t2) as t2' eqn:E2.
      revert E1 E2 H2. destruct H1. 
      + intros H1. inversion H1.
      + intros H2. inversion H2. subst. clear H2.


Show.
*)
