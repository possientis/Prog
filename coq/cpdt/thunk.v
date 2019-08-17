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

(* direct proof, using cofix tactic                                             *)
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





