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
        | left p  => Ex true (conj (fun _ => eq_refl) (fun _ => p))
        | right p => Ex false (conj _ _)
    end)
    (fun q => _)
).
    - intros H1. exfalso. apply p. assumption.
    - intros H1. inversion H1.
    - destruct q as [b [H1 H2]]. destruct b.
        + left. apply H2. reflexivity.
        + right. intros H3. apply H1 in H3. inversion H3.
Defined.

Open Scope type_scope.

Definition L7 : forall (X Y:Prop), {X} + {Y} -> X + Y.
Proof.
    intros X Y [H1|H1].
    - left. assumption.
    - right. assumption.
Defined.

Definition L8 : forall (X Y:Prop), X + Y -> {X} + {Y}.
Proof.
    intros X Y [H1|H1].
    - left. assumption.
    - right. assumption.
Qed.

Definition L9 : forall (X Y:Prop), {X} + {Y} -> X + Y :=
    fun (X Y:Prop) (q:{X} + {Y}) =>
        match q with
        | left p    => inl p
        | right p   => inr p
        end.

Definition L10 : forall (X Y:Prop), X + Y -> {X} + {Y} :=
    fun (X Y:Prop) (q:X + Y) =>
        match q with
        | inl p     => left p
        | inr p     => right p
        end.


Definition L11 : forall (n:nat), (n = 0) + Sig (fun k => n = S k).
Proof.
    intros n. destruct n as [|n].
    - left. reflexivity.
    - right. exact (Ex n eq_refl).
Defined.

Theorem Lawvere1 : forall (X Y:Type), 
    (exists (F:X -> (X -> Y)), forall (g:X -> Y), exists (x:X), F x = g) -> 
    forall (g:Y -> Y), exists (y:Y), g y = y.
Proof.
    intros X Y [F H] g. 
    destruct (H (fun u => g (F u u))) as [x H'].
    exists (F x x). change ((fun u => g (F u u)) x = F x x). 
    rewrite <- H'. reflexivity.
Qed.

(* Not a very useful theorem to prove the existence of fixed points it seems.   *)
(* It will not apply to Y = 0, it will apply to Y = 1, but for Y = 2 or bigger  *)
(* there is no sujection from X to Y^X... So the theorem seems useful to prove  *)
(* that no surjection exists between X and X -> Y, simply by exhibiting an fp   *)
Theorem Lawvere2 : forall (X Y:Type) (F: X -> (X -> Y)),
    (forall (g:X -> Y), exists (x:X), F x = g) ->
    (forall (g:Y -> Y), exists (y:Y), g y = y).
Proof.
    intros X Y F H. apply Lawvere1 with X. exists F. assumption.
Qed.

(* Computational version of Lawvere's theorem.                                  *)
Definition Lawvere3 : forall (X Y:Type) (F:X -> X -> Y),
    (forall (g:X -> Y), Sig (fun x => F x = g)) ->
    (forall (g:Y -> Y), Sig (fun y => g y = y)).
Proof.
    intros X Y F H g.
    destruct (H (fun u => g (F u u))) as [x H'].
    exists (F x x). change ((fun u => g (F u u)) x = F x x). 
    rewrite <- H'. reflexivity.
Qed.

Definition L12 : forall (B:Type) (a b:B),
    (forall (x:B), {x = a} + {x = b}) -> 
    (forall (p:B -> Type), p a -> p b -> forall (x:B), p x).
Proof.
    intros B a b q p Ha Hb x. destruct (q x) as [H1|H1]; rewrite H1; assumption.
Defined.

Definition L13 : forall (B:Type) (a b:B),
    (forall (p:B -> Type), p a -> p b -> forall (x:B), p x) ->
    (forall (x:B), {x = a} + {x = b}).
Proof.
    intros B a b q x. apply (q (fun x => {x = a} + {x = b})).
    - left. reflexivity.
    - right. reflexivity.
Defined.



