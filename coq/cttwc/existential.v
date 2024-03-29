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


Definition L20 : forall (a:Type) (p:a -> Prop),
    (exists (x:a), p x) <-> forall (A:Prop), (forall (x:a), p x -> A) -> A.
Proof.
refine (
    fun (a:Type) (p:a -> Prop) => conj
        (fun (H:exists (x:a), p x) =>
            match H with
            | ex_intro _ x H1  =>
                fun (A:Prop) (H2:forall (x:a), p x -> A) => H2 x H1
            end)
        (fun (H1:forall (A:Prop), (forall (x:a), p x -> A) -> A) => 
            H1 (exists (x:a), p x) (fun (x:a) (H2:p x) => ex_intro p x H2))).
Defined.

Definition L21 : forall (a:Type) (p q:a -> Prop),
    (forall (x:a), p x <-> q x) -> 
    (forall (x:a), p x) <-> (forall (x:a), q x).
Proof.
    intros a p q H1. split; intros H2 x; destruct (H1 x) as [H3 H4].
    - apply H3. apply H2.
    - apply H4. apply H2.
Qed.

Definition L22 : forall (a:Type) (p q:a -> Prop),
    (forall (x:a), p x <-> q x) -> 
    (forall (x:a), p x) <-> (forall (x:a), q x).
Proof.
refine (
    fun (a:Type) (p q:a -> Prop) (H1:forall (x:a), p x <-> q x) => conj
        (fun (H2:forall (x:a), p x) (x:a) =>
            match (H1 x) with
            | conj H3 H4    => H3 (H2 x)
            end)
        (fun (H2:forall (x:a), q x) (x:a) =>
            match (H1 x) with 
            | conj H3 H4    => H4 (H2 x)
            end
)).
Defined.

Definition L23 : forall (a:Type) (p q:a -> Prop),
    (forall (x:a), p x <-> q x) -> 
    (exists (x:a), p x) <-> (exists (x:a), q x).
Proof.
    intros a p q H1; split; intros [x H2]; 
    destruct (H1 x) as [H3 H4]; exists x.
    - apply H3. exact H2.
    - apply H4. exact H2.
Qed.

Definition L24 : forall (a:Type) (p q:a -> Prop),
    (forall (x:a), p x <-> q x) -> 
    (exists (x:a), p x) <-> (exists (x:a), q x).
Proof.
refine (
    fun (a:Type) (p q:a -> Prop) (H1:forall (x:a), p x <-> q x) => conj
        (fun (H2:exists (x:a), p x) =>
            match H2 with
            | ex_intro _ x H2   =>
                match (H1 x) with
                | conj H3 H4    => ex_intro q x (H3 H2)
                end
            end)
        (fun (H2:exists (x:a), q x) =>
            match H2 with
            | ex_intro _ x H2   =>
                match (H1 x) with
                | conj H3 H4    => ex_intro p x (H4 H2)
                end
            end)
).
Defined.

Definition L25 : forall (a:Type) (p:a -> Prop) (A:Prop),
    (exists (x:a), p x) /\ A <-> exists (x:a), p x /\ A.
Proof.
    intros a p A. split.
    - intros [[x H1] H2]. exists x. split.
        + exact H1.
        + exact H2.
    - intros [x [H1 H2]]. split.
        + exists x. exact H1.
        + exact H2.
Qed.

Definition L26 : forall (a:Type) (p:a -> Prop) (A:Prop),
    (exists (x:a), p x) /\ A <-> exists (x:a), p x /\ A.
Proof.
refine (
    fun (a:Type) (p:a -> Prop) (A:Prop) => conj
        (fun (H1: (exists (x:a), p x) /\ A) =>
            match H1 with
            | conj (ex_intro _ x H1) H2 => ex_intro (fun (x:a) => p x /\ A) x (conj H1 H2)
            end)
        (fun (H1: exists (x:a), p x /\ A) =>
            match H1 with
            | ex_intro _ x (conj H1 H2) => conj (ex_intro p x H1) H2
            end
)).
Defined.

Theorem Barber : forall (a:Type) (p:a -> a -> Prop),
    ~exists (x:a), forall (y:a), p x y <-> ~ p y y.
Proof.
    intros a p [x H]. destruct (H x) as [H1 H2];
    apply H1; apply H2; intros H3; apply H1; assumption.
Qed.

Definition L27 : forall (a:Type) (p:a -> a -> Prop),
    ~exists (x:a), forall (y:a), p x y <-> ~ p y y.
Proof.
refine (
    fun (a:Type) (p:a -> a -> Prop) =>
        fun (H: exists (x:a), forall (y:a), p x y <-> ~p y y ) =>
            match H with
            | ex_intro _ x H    =>
                match (H x) with
                | conj H1 H2 => 
                    let px := 
                        H2 (fun (qx:p x x) => H1 qx qx)
                    in H1 px px
                end
            end
).
Defined.


Definition LawRussell : forall (A:Prop), ~(A <-> ~A).
Proof.
    intros A [H1 H2]. apply H1; apply H2; intros H3; apply H1; assumption.
Qed.

Definition L28 : forall (A:Prop), ~(A <-> ~A).
Proof.
refine (
    fun (A:Prop) (H:A <-> ~A) => 
        match H with
        | conj H1 H2 => 
            let p :=
                H2 (fun (x:A) => H1 x x)
            in H1 p p
        end
).
Defined.

Definition L29 : forall (a:Type) (p:a -> a -> Prop),
    ~exists (x:a), forall (y:a), p x y <-> ~ p y y.
Proof.
refine (
    fun (a:Type) (p:a -> a -> Prop) =>
        fun (H:exists (x:a), forall (y:a), p x y <-> ~ p y y ) =>
            match H with
            | ex_intro _ x H => LawRussell (p x x) (H x)
            end
).
Defined.

Definition FixedPoint (a:Type) (f:a -> a) (x:a) : Prop := f x = x.

Arguments FixedPoint {a}.

Definition HasFixedPoint (a:Type) (f:a -> a) : Prop :=
    exists (x:a), FixedPoint f x.

Arguments HasFixedPoint {a}.

Definition L30 : ~ HasFixedPoint negb.
Proof.
    unfold HasFixedPoint. unfold FixedPoint. intros [b H]. 
    destruct b; inversion H.
Qed.

Definition L31 : ~ HasFixedPoint (fun (A:Prop) => ~A).
Proof.
    unfold HasFixedPoint. unfold FixedPoint. intros [A H1].
    apply (LawRussell A). split; intros H2.
    - rewrite <- H1 in H2. assumption.
    - rewrite H1 in H2. assumption.
Qed.

Definition Surjective (a b:Type) (f:a -> b) : Prop :=
    forall (y:b), exists (x:a), f x = y.

Arguments Surjective {a} {b}.

Theorem Lawvere : forall (X Y:Type), 
    (exists (F:X -> (X -> Y)), Surjective F) -> 
    forall (f:Y -> Y), HasFixedPoint f.
Proof.
    intros X Y [F H] f. unfold Surjective in H. 
    unfold HasFixedPoint. unfold FixedPoint.
    destruct (H (fun u => f (F u u))) as [x H'].
    exists (F x x). change ((fun u => f (F u u)) x = F x x). 
    rewrite <- H'. reflexivity.
Qed.

Definition Rewrite : forall (a:Type) (x y:a) (p:a -> Prop),
    x = y -> p x -> p y.
Proof.
    intros a x y p E H. rewrite <- E. assumption.
Qed.

Definition L32 : forall (a:Type) (x y:a) (p:a -> Prop), 
    x = y -> p x -> p y.
Proof.
refine (
    fun (a:Type) (x y:a) (p:a -> Prop) (E:x = y) (H:p x) =>
        match E with
        | eq_refl _ => H
        end
).
Qed.

Definition CongFun : forall (a b:Type) (f g:a -> b) (x:a), f = g -> f x = g x.
Proof.
refine (
    fun (a b:Type) (f g:a -> b) (x:a) (E:f = g) =>
        match E with
        | eq_refl _ => eq_refl (f x)
        end
).
Qed.

Arguments CongFun {a} {b} {f} {g}.

Definition L33 : forall (X Y:Type), 
    (exists (F:X -> (X -> Y)), Surjective F) -> 
    forall (f:Y -> Y), HasFixedPoint f.
Proof.
refine (
    fun (X Y:Type) (H:exists (F:X -> (X -> Y)), Surjective F) =>
        fun (f:Y -> Y) => 
            match H with
            | ex_intro _ F H =>
                match H (fun u => f (F u u)) with
                | ex_intro _ x H'   => 
                    ex_intro _ (F x x) 
                        (@CongFun X Y (fun u => f (F u u)) (F x) x (eq_sym H'))
                end
            end
).
Qed.

Definition Cantor : forall (X:Type), ~ exists (f:X -> (X -> bool)), Surjective f.
Proof.
    intros X H. assert (forall (f:bool -> bool), HasFixedPoint f) as H'.
        { apply Lawvere with X. assumption. }
    apply L30. apply H'.
Qed.

Definition Cantor' : forall (X:Type), ~ exists (f:X -> (X -> Prop)), Surjective f.
Proof.
    intros X H. assert (forall (f:Prop -> Prop), HasFixedPoint f) as H'.
        { apply Lawvere with X. assumption. }
    apply L31. apply H'.
Qed.

Inductive Void : Type :=.

Definition absurd (x:Void) : Void :=
    match x with end.

Lemma L34 : ~ HasFixedPoint absurd.
Proof.
    unfold HasFixedPoint. intros [x H]. inversion x.
Qed.

Lemma L35 : ~HasFixedPoint absurd.
Proof.
refine (
    fun (p:HasFixedPoint absurd) =>
        match p with
        | ex_intro _ x H    => 
            match x with end
        end
).
Qed.

Definition L36 (x : bool * bool) : bool * bool :=
    match x with
    | (b1,b2)   => (negb b1, b2)
    end.

Definition L37: ~HasFixedPoint L36.
Proof.
    unfold HasFixedPoint, FixedPoint, L36. intros [x H].
    destruct x as [b1 b2]. destruct b1; inversion H.
Qed.

Definition L38: ~HasFixedPoint S.
Proof.
    unfold HasFixedPoint, FixedPoint. intros [n H].
    revert H. revert n. induction n as [|n IH]; intros H.
    - inversion H.
    - inversion H. apply IH. assumption.
Qed.

Definition L39 (a:Type) : Type := a -> bool.

Definition cast (a b:Type) (p:a = b) (x:a) : b :=
    match p with
    | eq_refl _  => x
    end.

Lemma cast_cast_is_id : forall (a b:Type) (x:a) (p:a = b),
    cast b a (eq_sym p) (cast a b p x) = x.
Proof.
   intros a b x p. unfold cast. destruct p. simpl. reflexivity.
Qed.


Definition L41: ~HasFixedPoint L39.
Proof.
    unfold HasFixedPoint, FixedPoint, L39. intros [a H].
    apply Cantor with a.
    remember (fun (x:a) => cast a (a -> bool) (eq_sym H) x) as f eqn:E. 
    exists f. unfold Surjective. intros y.
    remember (cast (a -> bool) a H y) as x eqn:H1.
    exists x. rewrite E. rewrite H1. simpl.
    apply cast_cast_is_id.
Qed.

Definition L42 : forall (f:True -> True), HasFixedPoint f.
Proof.
    intros f. unfold HasFixedPoint, FixedPoint.
    exists I. destruct (f I). reflexivity.
Qed.

Definition L43 : forall (f:True -> True), HasFixedPoint f.
Proof.
refine (
    fun (f:True -> True) =>
        ex_intro _ I
            match (f I) as x return x = I with
            | I => eq_refl I
            end
).
Qed.

Definition L44 : ~ HasFixedPoint (fun (A:Prop) => ~A).
Proof.
    intros [X H1]. unfold FixedPoint in H1.
    assert (HasFixedPoint (fun (x:False) => x)) as H2.
        { apply Lawvere with X. unfold not in H1. rewrite H1.
          exists (fun x => x). unfold Surjective. intros y.
          exists y. reflexivity. }
    unfold HasFixedPoint in H2. destruct H2 as [x H2].
    contradiction.
Qed.


