Definition Decider (a:Type) (p:a -> Prop) (f:a -> bool) : Prop :=
    forall (x:a), p x <-> f x = true.

Arguments Decider {a}.

Inductive Sig (a:Type) (p:a -> Type) : Type :=
| Ex : forall (x:a), p x -> Sig a p
.

Arguments Sig {a}.
Arguments Ex {a} {p}.

Definition Sig_proj1 (a:Type) (p:a -> Type) (y:Sig p) : a :=
    match y with
    | Ex x _ => x
    end.

Arguments Sig_proj1 {a} {p}.
 
Definition Sig_proj2 (a:Type) (p:a -> Type) (y:Sig p) : p (Sig_proj1 y) :=
    match y with
    | Ex x H => H
    end.


Definition L1 : forall (a:Type) (p:a -> Prop),
    Sig (Decider p) -> forall (x:a), {p x} + {~ p x}.
Proof.
    intros a p H1.  destruct H1 as [f H1]. intros x.
    unfold Decider in H1. destruct (f x) eqn:E.
    - left. apply H1. assumption.
    - right. intros H2. apply H1 in H2. rewrite E in H2. inversion H2.
Defined.

Definition L2 : forall (a:Type) (p:a -> Prop),
    (forall (x:a), {p x} + {~p x}) -> Sig (Decider p).
Proof.
    intros a p q. remember 
        (fun x =>
            match q x with
            | left _    => true
            | right _   => false
            end) as f eqn:F.
    assert (Decider p f) as H1.
        { unfold Decider. intros x. split; intros H1.
            { rewrite F. destruct (q x) as [H2|H2].
                { reflexivity. }
                { exfalso. apply H2. assumption. }}
            { rewrite F in H1. destruct (q x) as [H2|H2].
                { assumption. }
                { inversion H1. }}}
    exact (Ex f H1).
Defined.

Inductive Equiv : Type -> Type -> Type :=
| mkEquiv : forall (a b:Type), (a -> b) -> (b -> a) -> Equiv a b
.

Arguments mkEquiv {a} {b}.

Notation "a <=> b" := (Equiv a b) 
    (at level 50, no associativity) : sigma_scope.

Open Scope sigma_scope.

Definition L3 : forall (a:Type) (p:a -> Prop),
    (forall (x:a), {p x} + {~p x}) <=> Sig (Decider p).
Proof.
    intros a p. exact (mkEquiv (L2 a p) (L1 a p)).
Qed.

Definition L4 : forall (a:Type) (p:a -> Prop), Sig p -> (exists (x:a), p x).
Proof.
    intros a p [x H1]. exists x. assumption.
Defined.

Inductive Inhabited (a:Type) : Prop :=
| mkInhabited : forall (x:a), Inhabited a
.

Arguments mkInhabited {a}.

Lemma L5 : forall (a:Type) (p:a -> Prop),
    Inhabited (Sig p) <-> exists (x:a), p x.
Proof.
    intros a p. split.
    - intros [[x H1]]. exists x. assumption.
    - intros [x H1]. exact (mkInhabited (Ex x H1)).
Qed.

Definition L6 : forall (X:Prop), 
    {X} + {~X} <=> Sig (fun b => X <-> b = true).
Proof.
intros X.
refine (mkEquiv
    (fun q => 
        match q with
        | left p  => Ex true _
        | right p => Ex false _
    end)
    _
).
Show.





