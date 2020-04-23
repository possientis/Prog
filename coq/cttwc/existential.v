(* The needed primitives                                                        *)
Variable Exists   : forall (a:Type), (a -> Prop) -> Prop. 
Variable mkExists : forall (a:Type) (p:a -> Prop) (x:a), p x -> Exists a p.
Variable ExistsInd : forall (a:Type) (p:a -> Prop) (c:Exists a p -> Prop), (forall (x:a)(q:p x), c (mkExists a p x q)) -> forall (e:Exists a p), c e.
Definition ExistsE : forall (a:Type) (p:a -> Prop) (A:Prop), (forall (x:a), p x -> A) -> Exists a p -> A := 
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

Definition L5 : forall (a:Type) (p q : a -> Prop),
    Exists (fun x => p x \/ q x) <-> Exists p \/ Exists q.
Proof.
    intros a p q. split.
    - intros H. apply (ExistsE a (fun x => p x \/ q x)).
        + intros x [H'|H'].
            { left.  apply (mkExists x). exact H'. }
            { right. apply (mkExists x). exact H'. }
        + exact H.
    - intros [H|H].
        + apply (ExistsE a p).
            { intros x H'. apply (mkExists x). left. exact H'. }
            { assumption. }
        + apply (ExistsE a q).
            { intros x H'. apply (mkExists x). right. exact H'. }
            { assumption. }
Qed.

Definition L6 : forall (a:Type) (p q : a -> Prop),
    Exists (fun x => p x \/ q x) <-> Exists p \/ Exists q.
Proof.
refine (
    fun (a:Type) (p q:a -> Prop) => conj
        (fun (H:Exists (fun x => p x \/ q x)) => 
            ExistsE a (fun x => p x \/ q x) (Exists p \/ Exists q)
                (fun (x:a) (H':p x \/ q x) =>
                    match H' with
                    | or_introl H'  => or_introl (mkExists x H')
                    | or_intror H'  => or_intror (mkExists x H')
                    end) H)
        (fun (H:Exists p \/ Exists q) => 
            match H with
            | or_introl H   => ExistsE a p (Exists (fun x => p x \/ q x)) 
                (fun (x:a) (H':p x) => mkExists x (or_introl H')) H
            | or_intror H   => ExistsE a q (Exists (fun x => p x \/ q x))
                (fun (x:a) (H':q x) => mkExists x (or_intror H')) H
            end)).
Defined.

Definition L7 : forall (a:Type) (p:a -> Prop),
    Exists p -> ~ forall (x:a), ~ p x.
Proof.
    intros a p H1 H2. apply (ExistsE a p).
    - intros x H3. apply (H2 x). exact H3.
    - exact H1.
Qed.

Definition L8 : forall (a:Type) (p:a -> Prop), Exists p -> ~ forall (x:a), ~ p x 
:=  fun (a:Type) (p:a -> Prop) =>
        fun (H1:Exists p) (H2:forall (x:a), ~ p x) =>
            ExistsE a p False H2 H1.
