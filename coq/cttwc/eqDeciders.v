Definition EqDecider (a:Type) (f:a -> a -> bool) : Prop :=
    forall (x y:a), x = y <-> f x y = true.
 
Arguments EqDecider {a}.


Definition Discrete (a:Type) : Prop := exists (f:a -> a -> bool), EqDecider f.

Fixpoint eqNat (n m:nat) : bool :=
    match n, m with
    | 0, 0          => true
    | 0, (S _)      => false
    | (S _), 0      => false
    | (S n), (S m)  => eqNat n m
    end.

Definition L1 : EqDecider eqNat.
Proof.
    unfold EqDecider. induction x as [|x IH]; intros y.
    - split; intros H; destruct y.
        + reflexivity.
        + inversion H.
        + reflexivity.
        + inversion H.
    - split; intros H; destruct y.
        + inversion H.
        + simpl. apply IH. inversion H. reflexivity.
        + inversion H.
        + simpl in H. apply IH in H. rewrite H. reflexivity.
Qed.

Definition L2 : forall (a:Type), Discrete a -> forall (x y:a), x = y \/ x <> y.
Proof.
    intros a. unfold Discrete, EqDecider. intros [f H] x y.
    destruct (f x y) eqn:E.
    - left. apply H. assumption.
    - right. intros H'. apply H in H'. rewrite H' in E. inversion E.
Qed.

Definition eqBool (x y:bool) : bool :=
    match x, y with
    | true, true    => true
    | false, true   => false
    | true, false   => false
    | false, false  => true
    end.

Definition L3 : EqDecider eqBool.
Proof.
    unfold EqDecider. intros x y. destruct x; destruct y; simpl; split; intros H.
    - reflexivity.
    - reflexivity.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - reflexivity.
    - reflexivity.
Qed.

Definition L4 : Discrete nat.
Proof.
    unfold Discrete. exists eqNat. apply L1.
Qed.

Definition L5 : Discrete bool.
Proof.
    unfold Discrete. exists eqBool. apply L3.
Qed.

Open Scope type_scope.

Definition eqProd (a b:Type) (f:a -> a -> bool) (g:b -> b -> bool) (p q:a * b) : bool :=
    match p, q with
    | (x,y), (x',y') => 
        match (f x x'), (g y y') with
        | true, true    => true
        | _,_           => false
        end
    end.

Arguments eqProd {a} {b}.

Definition L6 : forall (a b:Type) (f:a -> a -> bool) (g:b -> b -> bool),
    EqDecider f -> EqDecider g -> EqDecider (eqProd f g).
Proof.
    unfold EqDecider. intros a b f g Hf Hg [x y] [x' y']. split; intros H.
    - inversion H. subst. simpl. 
      destruct (Hf x' x') as [H1 H2].
      destruct (Hg y' y') as [H3 H4].
      rewrite H1, H3
        + reflexivity.
        + reflexivity.
        + reflexivity.
        + reflexivity.
    - simpl in H.

Show.

