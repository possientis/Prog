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

(* was useful when dealing with stream                                          *)
Definition frob (a:Type) (t:Thunk a) : Thunk a :=
    match t with
    | Answer x  => Answer x
    | Think t'  => Think t'
    end.

Arguments frob {a}.

Lemma frob_same : forall (a:Type) (t:Thunk a), t = frob t.
Proof. intros a. destruct t as [x|t]; reflexivity. Qed.

Arguments frob_same {a}.

CoInductive thunk_eq (a:Type) : Thunk a -> Thunk a -> Prop :=
| Answer_eq : forall (x y:a), x = y -> thunk_eq a (Answer x) (Answer y)
| Think_eq  : forall (t1 t2:Thunk a), 
    thunk_eq a t1 t2 -> thunk_eq a (Think t1) (Think t2)
.

Arguments thunk_eq {a}.

Lemma thunk_eq_answer : forall (a:Type) (x y:a),
    thunk_eq (Answer x) (Answer y) -> x = y.
Proof.
    intros a x y H. inversion H. assumption.
Qed.

Lemma thunk_eq_think : forall (a:Type) (t1 t2:Thunk a),
    thunk_eq (Think t1) (Think t2) -> thunk_eq t1 t2.
Proof.
    intros a t1 t2 H. inversion H. assumption.
Qed.

Lemma thunk_eq_ans_thk : forall (a:Type) (x:a) (t:Thunk a),
    ~thunk_eq (Answer x) (Think t).
Proof.
    intros a x t H. inversion H.
Qed.

Lemma thunk_eq_thk_ans : forall (a:Type) (x:a) (t:Thunk a),
    ~thunk_eq (Think t) (Answer x).
Proof.
    intros a x t H. inversion H.
Qed.

Lemma thunk_eq_coind : forall (a:Type) (R:Thunk a -> Thunk a -> Prop),
    (forall (x y:a), R (Answer x) (Answer y) -> x = y)           ->
    (forall (t1 t2:Thunk a), R (Think t1) (Think t2) -> R t1 t2) ->
    (forall (x:a)(t2:Thunk a), ~R (Answer x) (Think t2))         ->
    (forall (y:a)(t1:Thunk a), ~R (Think t1) (Answer y))         ->
    (forall (t1 t2:Thunk a), R t1 t2 -> thunk_eq t1 t2).
Proof.
    intros a R H1 H2 H3 H4. cofix coIH. intros [x|t1] [y|t2] H.
    - apply H1 in H. rewrite H. constructor. reflexivity.
    - exfalso. apply (H3 x t2). assumption.
    - exfalso. apply (H4 y t1). assumption.
    - apply H2 in H. constructor. apply coIH. assumption.
Qed.

Arguments thunk_eq_coind {a}.

(* direct proof using cofix tactic                                              *)
Lemma thunk_eq_refl : forall (a:Type) (t:Thunk a), thunk_eq t t.
Proof.
    intros a. cofix coIH. intros [x|t].  - constructor. reflexivity.
    - constructor. apply coIH.
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
    intros a. cofix coIH. intros t1 t2 H. destruct H as [x y|t1 t2].
    - constructor. symmetry. assumption.
    - constructor. apply coIH. assumption.
Qed.

(* proof using coinduction principle                                            *)
Lemma thunk_eq_sym' : forall (a:Type) (t1 t2:Thunk a),
    thunk_eq t1 t2 -> thunk_eq t2 t1.
Proof.
    intros a t1 t2 H. apply (thunk_eq_coind (fun x y => thunk_eq y x)).
    - clear t1 t2 H. 
      intros x y H. symmetry. apply thunk_eq_answer. assumption.
    - clear t1 t2 H. 
      intros t1 t2 H. apply thunk_eq_think. assumption.
    - clear t1 t2 H. 
      intros x t. apply thunk_eq_thk_ans.
    - clear t1 t2 H. 
      intros x t. apply thunk_eq_ans_thk.
    - assumption.
Qed.

(* direct proof using cofix tactic                                              *)
Lemma thunk_eq_trans : forall (a:Type) (t1 t2 t3:Thunk a),
    thunk_eq t1 t2 -> thunk_eq t2 t3 -> thunk_eq t1 t3.
Proof.
    intros a. cofix  coIH. intros t1 t2 t3 H. revert t3. destruct H.
    - subst. intros t3 H. assumption.
    - intros t3. remember (Think t2) as t2' eqn:E. 
      intros H'. revert E. destruct H'.
        + intros H1. inversion H1.
        + intros H1. inversion H1. subst. constructor.
          apply coIH with t2; assumption.
Qed.

(* proof using coinduction principle                                            *)
Lemma thunk_eq_trans' : forall (a:Type) (t1 t2 t3:Thunk a),
    thunk_eq t1 t2 -> thunk_eq t2 t3 -> thunk_eq t1 t3.
Proof.
    intros a t1 t2 t3 H1 H2.
    apply (thunk_eq_coind (fun x z => exists y, thunk_eq x y /\ thunk_eq y z)).
    - clear t1 t2 t3 H1 H2.
      intros x y [[z|t] [H1 H2]].
        + apply eq_trans with z; apply thunk_eq_answer; assumption.
        + inversion H1.
    - clear t1 t2 t3 H1 H2.
      intros t1 t2 [[z|t] [H1 H2]].
        + inversion H1.
        + exists t. split; apply thunk_eq_think; assumption.
    - clear t1 t2 t3 H1 H2.
      intros x t2 [[y|t1] [H1 H2]]. 
        + inversion H2.
        + inversion H1.
    - clear t1 t2 t3 H1 H2.
      intros y t1 [[x|t2] [H1 H2]]. 
        + inversion H1.
        + inversion H2.
    - exists t2. split; assumption.
Qed.


Notation "t1 == t2" := (thunk_eq t1 t2) (at level 90).


Lemma left_identity : forall (a b:Type) (x:a) (f:a -> Thunk b),
    (pure x) >>= f  ==  f x.
Proof.
    intros a b x f. unfold pure. 
    rewrite (frob_same (Answer x >>= f )). unfold bind. 
    simpl. destruct (f x) as [y|t] eqn:E; constructor.
    - reflexivity.
    - apply thunk_eq_refl.
Qed.

Lemma right_identity : forall (a:Type) (t:Thunk a),
    t >>= pure == t.
Proof.
    intros a. cofix coIH. intros t. rewrite (frob_same (t >>= pure)). simpl.
    destruct t as [x|t'] eqn:E.
    - unfold pure. constructor. reflexivity.
    - constructor. apply coIH.
Qed.

Lemma associativity : forall (a b c:Type),
    forall (t:Thunk a) (f:a -> Thunk b) (g:b -> Thunk c),
    t >>= f >>= g == t >>= (fun (x:a) => (f x) >>= g).
Proof.
    intros a b c. cofix coIH. intros t f g.
    rewrite (frob_same (t >>= f >>= g)).
    rewrite (frob_same (t >>= f)).
    rewrite (frob_same (t >>= (fun (x:a) => (f x) >>= g))).
    simpl. destruct t as [x|t1] eqn:E1.
    - rewrite (frob_same (f x >>= g)). simpl.
      destruct (f x) as [y|t2] eqn:E2.
        + destruct (g y) as [z|t3] eqn:E3; apply thunk_eq_refl.
        + apply thunk_eq_refl.
    - constructor. apply coIH.
Qed.


CoFixpoint fact (n acc:nat) : Thunk nat :=
    match n with
    | 0     => Answer acc
    | S n   => Think (fact n (S n * acc))
    end.

Fixpoint fact' (n acc:nat) : nat :=
    match n with
    | 0     => acc
    | S n   => fact' n (S n * acc)
    end.

Fixpoint fact3 (n acc:nat) : Thunk nat :=
    match n with
    | 0     => Answer acc
    | S n   => Think (fact3 n (S n * acc))
    end.

Inductive Eval (a:Type) : Thunk a -> a -> Prop :=
| EvalAnswer : forall (x:a), Eval a (Answer x) x
| EvalThink  : forall (t:Thunk a) (x:a), Eval a t x -> Eval a (Think t) x
.

Arguments Eval {a}.

(* Cannot believe this is useful                                                *)
Lemma eval_frob : forall (a:Type) (t:Thunk a) (x:a),
    Eval (frob t) x -> Eval t x.
Proof.
    intros a t x. rewrite <- frob_same. intros H. assumption.
Qed.

Lemma eval_fact : Eval (fact 5 1) 120.
Proof.
    repeat (apply eval_frob; simpl; constructor).
Qed.


(*
Compute (fact 5 1).
Compute (fact' 5 1).
Compute (fact3 5 1).
*)

Fail CoFixpoint fib (n:nat) : Thunk nat :=
    match n with
    | 0         => Answer 1
    | 1         => Answer 1
    | S (S n)   =>
        fib (S n) >>= (fun n1 =>
            fib n >>= (fun n2 =>
            Answer (n1 + n2)))
    end.



