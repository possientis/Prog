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

(*
Check Exists2.
Check mkExists2.
Check ExistsInd2.
Check ExistsE2.
*)


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

Definition L9 : forall (a:Type) (p:a -> Prop)(A:Prop),
    (Exists p -> A) <-> forall (x:a), p x -> A.
Proof.
    intros a p A. split; intros H.
    - intros x Hx. apply H. apply mkExists with x. exact Hx.
    - intros H'. apply (ExistsE a p).
        + exact H.
        + exact H'.
Qed.

Definition L10 : forall (a:Type) (p:a -> Prop)(A:Prop),
    (Exists p -> A) <-> forall (x:a), p x -> A.
Proof.
refine (
    fun (a:Type) (p:a -> Prop) (A:Prop) => conj
        (fun (H:Exists p -> A) (x:a) (Hx:p x)  => 
            H (mkExists x Hx)) 
        (fun (H:forall (x:a), p x -> A) (H':Exists p) =>
            ExistsE a p A H H'
)). 
Qed.

Definition L11 : forall (a:Type) (p:a -> Prop),
    ~~(Exists p) <-> ~ forall (x:a), ~ p x.
Proof.
    intros a p. split; intros H1 H2.
    - apply H1. intros H3. apply (ExistsE a p False).
        + intros x Hx. apply (H2 x). exact Hx.
        + exact H3.
    - apply H1. intros x Hx. apply H2. apply mkExists with x. exact Hx.
Qed.

Definition L12 : forall (a:Type) (p:a -> Prop),
    ~~(Exists p) <-> ~ forall (x:a), ~ p x.
Proof.
refine (
    fun (a:Type) (p:a -> Prop) => conj
        (fun (H1:~~Exists p) (H2: forall (x:a), ~ p x) => 
            H1 (fun (H3:Exists p) => 
                ExistsE a p False 
                    (fun (x:a) (Hx:p x) => H2 x Hx) 
                    H3))
        (fun (H1:~ forall (x:a), ~ p x) (H2:~Exists p) =>
            H1 (fun (x:a) (Hx:p x) => H2 (mkExists x Hx)))).
Qed.

Definition L13 : forall (a:Type) (p:a -> Prop),
    Exists (fun x => ~~p x) -> ~~Exists p.
Proof.
    intros a p H1 H2. apply (ExistsE a (fun x => ~~p x) False).
    - intros x Hx. apply Hx. intros Hx'. apply H2. 
      apply mkExists with x. exact Hx'.
    - exact H1.
Qed.

Definition L14 : forall (a:Type) (p:a -> Prop),
    Exists (fun x => ~~p x) -> ~~Exists p.
Proof.
refine (
    fun (a:Type) (p:a -> Prop) (H1:Exists (fun x => ~~p x)) (H2:~Exists p) =>
    ExistsE a (fun x => ~~p x) False
        (fun (x:a) (Hx:~~p x) => Hx (fun (Hx':p x) => H2 (mkExists x Hx')))
        H1
).
Qed.

Definition L15 : forall (A:Prop), A <-> exists (q:A), True. 
Proof.
    intros A. split; intros H.
    - exists H. apply I.
    - destruct H as [q H]. exact q.
Qed.



Definition L16 : forall (A:Prop), A <-> exists (q:A), True.
Proof.
refine (
    fun (A:Prop) => conj
        (fun (H:A) => ex_intro (fun (_:A) => True) H I)
        (fun (H:exists (q:A), True) =>
            match H with
            | ex_intro _ q _  => q
            end
)).
Qed.

Definition L17 : forall (a:Type) (x y:a), 
    x <> y <-> exists (p:a -> Prop), p x /\ ~p y.
Proof.
    intros a x y. split; intros H.
    - exists (fun (z:a) => x = z). split.
        + reflexivity.
        + exact H.
    - destruct H as [p [H1 H2]]. intros H. apply H2. 
      rewrite <- H. exact H1.
Qed.

Definition L18 : forall (a:Type) (x y:a), 
    x <> y <-> exists (p:a -> Prop), p x /\ ~p y.
Proof.
refine (
    fun (a:Type) (x y:a) => conj
        (fun (H:x <> y) => ex_intro _ (fun (z:a) => x = z) (conj (eq_refl x) H))
        (fun (H:exists (p:a -> Prop), p x /\ ~p y) =>
            match H with
            | ex_intro _ p H =>
                match H with
                | conj H1 H2 => 
                    fun (H:x = y) => H2 (eq_ind x p H1 y H)
                end
            end
        
)).
Qed.

Definition L19 : forall (a:Type) (p:a -> Prop),
    (exists (x:a), p x) <-> forall (A:Prop), (forall (x:a), p x -> A) -> A.
Proof.
    intros a p. split.
    - intros [x H1] A H2. apply H2 with x. exact H1.
    - intros H1. apply H1. intros x H2. exists x. exact H2.
Qed.

