Inductive Sequence (a:Type) : Type :=
| End  : a -> Sequence a
| Next : Sequence a -> Sequence a
.

Arguments End {a}.
Arguments Next {a}.

Fixpoint fmap (a b:Type) (f:a -> b) (xs:Sequence a) : Sequence b :=
    match xs with
    | End x     => End (f x)
    | Next xs   => Next (fmap a b f xs)
    end.

Arguments fmap {a} {b}.

Definition pure (a:Type) : a -> Sequence a := End.

Arguments pure {a}.

Fixpoint apply (a b:Type) (f : Sequence (a -> b)) (x:Sequence a) : Sequence b :=
    match f with
    | End f     =>
        match x with
        | End x     => End (f x)
        | Next xs   => Next (fmap f xs)
        end
    | Next fs   => Next (apply a b fs x)
    end.

Arguments apply {a} {b}.

Notation "f <*> x" := (apply f x) (at level 50).

Fixpoint bind (a b:Type) (f:a -> Sequence b) (x:Sequence a) : Sequence b :=
    match x with
    | End x     => f x
    | Next xs   => Next (bind a b f xs)
    end.

Lemma fmapApply : forall (a b:Type) (f:a -> b) (xs:Sequence a),
    fmap f xs = End f <*> xs.
Proof.
    intros a b f. destruct xs as [x|xs]; reflexivity.
Qed.

Arguments bind {a} {b}.

Notation "x >>= f" := (bind f x) (at level 50).

Definition ap (a b:Type) (f:Sequence (a -> b)) (x:Sequence a) : Sequence b :=
    f >>= (fun f => (x >>= fun x => End (f x))).

Arguments ap {a} {b}.

Lemma apIsApply : forall (a b:Type) (f:Sequence (a -> b)) (x:Sequence a),
    f <*> x = ap f x.
Proof.
    intros a b. induction f as [f|fs IH1].
    - induction x as [x|xs IH].
        + reflexivity.
        + unfold apply. unfold ap. unfold bind at 1. 
          unfold ap in IH. unfold bind at 1 in IH. 
          unfold bind. fold (xs >>= (fun x : a => End (f x))).
          rewrite <- IH. rewrite fmapApply. reflexivity.
    - intros x. simpl. rewrite IH1. reflexivity.
Qed.

