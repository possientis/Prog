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

Definition frob (a:Type) (t:Thunk a) : Thunk a :=
    match t with
    | Answer x  => Answer x
    | Think t'  => Think t'
    end.

Arguments frob {a}.

Lemma frob_same : forall (a:Type) (t:Thunk a), t = frob t.
Proof. intros a. destruct t as [x|t]; reflexivity. Qed.



