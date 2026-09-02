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
    - induction x as [|x IH]; intros y.
        + rewrite H2, H1, H1. reflexivity.
        + rewrite (H2 (S x) y), (H2 x (S y)), IH. reflexivity.
Qed.

Definition L6 : forall (f:nat -> nat -> nat), Add2 f -> Add f.
Proof.
    unfold Add, Add2. intros f [H1 H2]. split.
    - assumption.
    - induction x as [|x IH]; intros y.
        + rewrite H2, H1, H1. reflexivity.
        + rewrite (H2 (S x) y), (IH (S y)), H2. reflexivity.
Qed.

Definition Hardt (f:nat -> nat) : Prop
    := f 0 = 0
    /\ (forall (n:nat), f (S n) = S (f (f n))).

Definition L7 : Hardt (fun x => x).
Proof.
    unfold Hardt. split.
    - reflexivity.
    - intros n. reflexivity.
Qed.


Definition L8 : forall (f:nat -> nat),
    Hardt f -> forall (n:nat), f n = n.
Proof.  
    unfold Hardt. intros f [H1 H2]. induction n as [|n IH].
    - assumption.
    - rewrite H2, IH, IH. reflexivity.
Qed.

Definition Hardt2 (f:nat -> nat) : Prop
    := f 0 = 0
    /\ (forall (n:nat), f (S n) = f (S (f n))).


Definition L9 : Hardt2 (fun x => x).
Proof.
    unfold Hardt2. split.
    - reflexivity.
    - intros n. reflexivity.
Qed.

(*
Definition L10 : forall (f:nat -> nat),
    Hardt2 f -> forall (n:nat), f n = n.
Proof.  
    unfold Hardt2. intros f [H1 H2]. induction n as [|n IH].
    - assumption.
    -
Show.
*)

Definition Spec1 (f:False -> nat) : Prop := (forall x, f x = 5).

Definition L10 : Spec1 (fun x => match x with end).
Proof.
    unfold Spec1. intros x. contradiction.
Qed.

Definition L11 : forall (f g:False -> nat), Spec1 f -> Spec1 g -> forall x, f x = g x.
Proof.
    unfold Spec1. intros f g H1 H2 x. contradiction.
Qed.

