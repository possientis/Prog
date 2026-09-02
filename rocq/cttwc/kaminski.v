Definition L1 : forall (f:bool -> bool) (x:bool), f (f (f x)) = f x.
Proof.
    intros f x. destruct x.
    - destruct (f true) eqn:E1.
        + rewrite E1. assumption.
        + destruct (f false) eqn:E2; assumption.
    - destruct (f false) eqn:E1.
        + destruct (f true) eqn:E2; assumption.
        + rewrite E1. assumption.
Qed.

Definition BoolRec : forall (p:bool -> Type), 
    p true  -> 
    p false -> 
    forall (x:bool), p x.
Proof.
    intros p H1 H2 x. destruct x; assumption.
Qed.

Definition L2 : forall (p:bool -> Prop) (x:bool), 
    (x = true -> p true) -> (x = false -> p false) -> p x.
Proof.
    intros p x H1 H2. destruct x.
    - apply H1. reflexivity.
    - apply H2. reflexivity.
Qed.

Definition Rewrite : forall (a:Type) (p:a -> Prop) (x y:a),
    x = y -> p x -> p y.
Proof.
    intros a p x y E H. rewrite <- E. assumption.
Qed.



Definition L3 : forall (f:bool -> bool) (x:bool), f (f (f x)) = f x.
Proof.
refine (
    fun (f:bool -> bool) (x:bool) => 
        match x as x' return f (f (f x')) = f x' with 
        | true  => L2 (fun x => f (f x) = x) (f true)
            (fun (q:f true = true) => 
                Rewrite bool (fun x => f x = true) true (f true) (eq_sym q) q)
            (fun (q:f true = false) => L2 (fun x => f x = false) (f false)
                (fun _ => q)
                (fun x => x))
        | false => L2 (fun x => f (f x) = x) (f false)
            (fun (q:f false = true) => L2 (fun x => f x = true) (f true)
                (fun x => x)
                (fun _ => q))
            (fun (q:f false = false) =>
                Rewrite bool (fun x => f x = false) false (f false) (eq_sym q) q)
        end
).
Qed.

