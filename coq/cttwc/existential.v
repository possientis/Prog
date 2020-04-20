(* The needed primitives                                                        *)
Variable Exists   : forall (a:Type), (a -> Prop) -> Prop. 
Variable mkExists : forall (a:Type) (p:a -> Prop) (x:a), p x -> Exists a p.
Variable ExistsInd : forall (a:Type) (p:a -> Prop) (c:Exists a p -> Prop), (forall (x:a)(q:p x), c (mkExists a p x q)) -> forall (e:Exists a p), c e.
Definition ExistsE : forall (a:Type) (p:a -> Prop) (A:Prop), 
    (forall (x:a), p x -> A) -> Exists a p -> A := 
    fun a p A H e => ExistsInd a p (fun _ => A) H e.

(* THese primitives exist                                                       *)
Inductive Exists2 (a:Type) (p:a -> Prop) : Prop :=
| mkExists2 : forall (x:a), p x -> Exists2 a p
.

Definition ExistsInd2 : forall (a:Type) (p:a -> Prop) (c:Exists2 a p -> Prop), 
    (forall (x:a)(q:p x), c (mkExists2 a p x q)) -> 
        forall (x:Exists2 a p), c x :=
    fun (a:Type) (p:a -> Prop) (c:Exists2 a p -> Prop) (f:forall (x:a) (q:p x), c (mkExists2 a p x q)) (e:Exists2 a p) =>
        match e with
        | mkExists2 _ _ x q => f x q
        end. 

Definition ExistsE2 : forall (a:Type) (p:a -> Prop) (A:Prop), 
    (forall (x:a), p x -> A) -> Exists2 a p -> A := 
    fun a p A H e => ExistsInd2 a p (fun _ => A) H e.

Check Exists2.
Check mkExists2.
Check ExistsInd2.
Check ExistsE2.



Arguments Exists {a}.
Arguments mkExists {a} {p}.


Definition L1 : forall (a:Type) (p:a -> Prop), ~(Exists p) <-> forall (x:a), ~ p x.
Proof.
    intros a p. split.
    - intros f x H. apply f. apply mkExists with x. assumption.
    - intros f H. apply (ExistsE a p). 
        + intros x H'. apply (f x). assumption.
        + assumption.
Qed.

Definition L2 : forall (a:Type) (p:a -> Prop), ~(Exists p) <-> forall (x:a), ~ p x.
Proof.
refine (
    fun (a:Type) (p:a -> Prop) => conj
        (fun (f:~Exists p) (x:a) (H:p x) => f (mkExists x H))
        (fun (f:forall (x:a), ~ p x) (H:Exists p) =>
            ExistsE a p False 
                (fun (x:a) (H':p x) => f x H') 
                H
)).
Defined.

Definition L3 : forall (a b:Type) (p:a -> b -> Prop),
    Exists (fun (x:a) => Exists (fun (y:b) => p x y)) -> 
    Exists (fun (y:b) => Exists (fun (x:a) => p x y)).
Proof.
    intros a b p H1. 
    apply (ExistsE a (fun (x:a) => Exists (fun (y:b) => p x y))).
    - intros x H2. apply (ExistsE b (fun (y:b) => p x y)).
        + intros y H3. apply (mkExists y). apply (mkExists x). exact H3.
        + exact H2.
    - exact H1.
Qed.


Definition L4 : forall (a b:Type) (p:a -> b -> Prop),
    Exists (fun (x:a) => Exists (fun (y:b) => p x y)) -> 
    Exists (fun (y:b) => Exists (fun (x:a) => p x y)).
Proof.
refine (
    fun (a b:Type) (p:a -> b -> Prop) =>
        fun (H1:Exists (fun (x:a) => Exists (fun (y:b) => p x y))) =>
            ExistsE a (fun (x:a) => Exists (fun (y:b) => p x y)) _
                (fun (x:a) (H2: Exists (fun (y:b) => p x y)) => 
                    ExistsE b (fun (y:b) => p x y) _
                        (fun (y:b) (H3:p x y) =>
                            mkExists y (mkExists x H3))
                        H2)
                H1
).
Defined.

