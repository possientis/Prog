Definition Add (f:nat -> nat -> nat) : Prop 
    := (forall (y:nat), f 0 y = y) 
    /\ (forall (x y:nat), f (S x) y = S (f x y)).

(* uniqueness up to functional extensionality                                   *)
Definition L1 : forall (f g:nat -> nat -> nat),
    Add f -> Add g -> forall (x y:nat), f x y = g x y.
Proof.
    intros f g [H1 H2] [H3 H4]. induction x as [|x IH]; intros y.
    - rewrite H1, H3. reflexivity.
    - rewrite H2, H4, IH. reflexivity.
Qed.

(* existence                                                                    *)
Definition L2 : Add (fun (x y:nat) => x + y).
Proof.
    unfold Add. split; intros y; reflexivity.
Qed.

Definition FunExt : Prop := forall (a b:Type) (f g:a -> b), 
    (forall (x:a), f x = g x) -> f = g.

Definition Ack (f:nat -> nat -> nat) : Prop 
    := (forall (y:nat), f 0 y = S y)
    /\ (forall (x:nat), f (S x) 0 = f x 1)
    /\ (forall (x y:nat), f (S x) (S y) = f x (f (S x) y)).

(* uniqueness up to functional extensionality                                   *)
Definition L3 : forall (f g:nat -> nat -> nat),
    Ack f -> Ack g -> forall (x y:nat), f x y = g x y.
Proof.
    intros f g [H1 [H2 H3]] [H4 [H5 H6]]. induction x as [|x IH1]; intros y.
    - rewrite H1, H4. reflexivity.
    - induction y as [|y IH2]. 
        + rewrite H2, H5. apply IH1.
        + rewrite H3, H6. rewrite IH2. apply IH1.
Qed.

(* existence                                                                    *)
Definition L4 : Ack (fix f (x:nat) : nat -> nat :=
    match x with
    | 0     => S
    | S x   => fix g (y:nat) : nat :=
        match y with
        | 0     => f x 1
        | S y   => f x (g y)
        end
    end).  
Proof.
    unfold Ack. split.
    - intros y. reflexivity.
    - split.
        + destruct x as [|x]; reflexivity.
        + intros x. destruct y as [|y]; reflexivity.
Qed.

Definition Add2 (f:nat -> nat -> nat) : Prop
    := (forall (y:nat), f 0 y = y)
    /\ (forall (x y:nat), f (S x) y = f x (S y)).

Definition L5 : forall (f:nat -> nat -> nat), Add f -> Add2 f.
Proof.
    unfold Add, Add2. intros f [H1 H2]. split.
    - assumption.
    -

Show.
