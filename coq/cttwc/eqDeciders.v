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
    - simpl in H. destruct (f x x') eqn:Ef; destruct (g y y') eqn:Eg.
        + apply Hf in Ef. apply Hg in Eg. subst. reflexivity.
        + inversion H.
        + inversion H.
        + inversion H.
Qed.

Definition L7 : forall (a b:Type), Discrete a -> Discrete b -> Discrete (a * b).
Proof.
    intros a b [f Hf] [g Hg]. unfold Discrete. exists (eqProd f g).
    apply L6; assumption.
Qed.

Definition eqFalse : False -> False -> bool := 
    fun (p:False) => match p with end.

Definition L8 : Discrete False.
Proof.
    unfold Discrete. exists eqFalse. unfold EqDecider.
    intros x y. contradiction.
Qed.

Definition eqUnit : unit -> unit -> bool :=
    fun (x y:unit) => 
        match x,y with 
        | tt,tt => true    
        end.

Definition L9 : Discrete unit.
Proof.
    unfold Discrete. exists eqUnit. unfold EqDecider.
    intros x y. destruct x. destruct y. simpl. split; intros H; reflexivity. 
Qed.

Fixpoint leb (n m:nat) : bool :=
    match n with
    | 0     => true
    | S n   =>
        match m with
        | 0     => false
        | S m   => leb n m
        end
    end.

Open Scope nat_scope.
Definition L10 : forall (n m:nat), leb n m = true <-> exists (k:nat), n + k = m.
Proof.
    induction n as [|n IH]; intros m; destruct m; split; intros H; simpl in H; simpl.
    - exists 0. reflexivity.
    - reflexivity.
    - exists (S m). reflexivity.
    - reflexivity.
    - inversion H.
    - destruct H as [k H]. inversion H.
    - apply IH in H. destruct H as [k H]. exists k. rewrite H. reflexivity.
    - apply IH. destruct H as [k H]. exists k. inversion H. reflexivity.
Qed.

Definition FunExt : Prop := forall (a b:Type) (f g:a -> b), 
    (forall (x:a), f x = g x) -> f = g.

Definition L11 : FunExt -> forall (f g:unit -> unit), f = g.
Proof.
    unfold FunExt. intros H f g. apply H. intros x.
    destruct x. destruct (f tt). destruct (g tt). reflexivity.
Qed.

Definition eqUnitUnit : (unit -> unit) -> (unit -> unit) -> bool.
