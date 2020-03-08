(* Leibniz symmetry                                                             *)
Definition L1 : forall (a:Type) (x y:a),
    (forall (p:a -> Prop), p x -> p y) -> (forall (p:a -> Prop), p y -> p x) :=
    fun (a:Type) =>
        fun(x y:a) =>
            fun (f: forall (p:a -> Prop), p x -> p y) =>
                fun (p:a -> Prop) => 
                    f (fun (z:a) => (p z -> p x)) (fun k => k).



Definition L2 : forall (a:Type) (x y:a),
    (forall (p:a -> Prop), p x -> p y) -> (forall (p:a -> Prop), p y -> p x).
Proof.
    intros a x y f p. 
    change ((fun z => p z -> p x) y).
    apply f.
    exact (fun z => z).
Qed.

(* All we need for propositional equality are 3 typed constants                 *)

(*
Variable Eq      : forall (X:Type), X -> X -> Prop.
Variable Refl    : forall (X:Type) (x:X), Eq X x x.
Variable Rewrite : forall (X:Type) (x y:X) (p:X -> Prop), Eq X x y -> p x -> p y.
*)

Inductive Eq (X:Type) : X -> X -> Prop :=
| Refl : forall (x:X), Eq X x x
.

Arguments Eq {X}.

Arguments Refl {X}.

Lemma Rewrite' : forall (X:Type) (x y:X) (p:X -> Prop), 
    Eq x y -> p x -> p y.
Proof.
    intros X x y p H H'. destruct H. assumption.
Qed.

Lemma EqInv3 : forall (X:Type) (x y:X), Eq x y -> x = y.
Proof.
    intros X x y H. destruct H. reflexivity.
Qed.

(* Do it with 'refine' first ...                                               *)
Definition EqInv2 : forall (X:Type) (x y:X), Eq x y -> x = y.
Proof. refine (
    fun (X:Type) =>
        fun (x y:X) =>
            fun (H:Eq x y) =>
                match H with
                | Refl _  => eq_refl
                end

).
Defined.

Definition EqInv : forall (X:Type) (x y:X), Eq x y -> x = y :=
    fun (X:Type) =>
        fun (x y:X) =>
            fun (H:Eq x y) =>
                match H with
                | Refl _  => eq_refl
                end.


Print EqInv.

(* Do it with 'refine' first ...                                                *)
Definition Rewrite2 : forall (X:Type) (x y:X) (p:X -> Prop), 
    Eq x y -> p x -> p y.
Proof. refine (
    fun (X:Type) =>
        fun(x y:X) =>
            fun (p:X -> Prop) =>
                fun (e:Eq x y) =>
                        match e in (Eq x' y') return (p x' -> p y') with 
                        | Refl x' => fun (z:p x') => z
                        end
).
Defined.

Definition Rewrite : forall (X:Type) (x y:X) (p:X -> Prop), 
    Eq x y -> p x -> p y 
    :=
    fun (X:Type) =>
        fun(x y:X) =>
            fun (p:X -> Prop) =>
                fun (e:Eq x y) =>
                        match e with 
                        | Refl x' => fun (z:p x') => z
                        end.

Arguments Rewrite {X} {x} {y}.


Definition L3 : Eq (negb true) false.
Proof. constructor. Qed.

Definition L4 : Eq (negb true) false := Refl false.

Definition L5 : Eq false (negb (negb false)) := Refl false.

(* Managed to write a term where @Rewrite is applied to 7 arguments *)
Definition L6 : Eq 0 0 := @Rewrite nat 0 0 
    (fun (n:nat) => Eq n 0 -> Eq n 0) 
    (Refl 0) 
    (fun x => x) 
    (Refl 0). 

(* Managed to write a term where @Rewrite is applied to 8 arguments *)
Definition L7 : Eq 0 0 := @Rewrite nat 0 0 
    (fun (n:nat) => Eq n 0 -> Eq n 0 -> Eq n 0) 
    (Refl 0) 
    (fun x _ => x) 
    (Refl 0) 
    (Refl 0). 

(* Usual Coq tactics, final proof term far from canonical                       *)
Definition L8 : ~(Eq True False).
Proof.
    intros E. inversion E. apply I.
Qed.

Definition L9 : ~(Eq True False).
Proof.
    intros E. change ((fun X => X) False).
    apply (Rewrite _ E). apply I.
Qed.

Definition L10 : ~(Eq True False).
Proof. refine (
    fun E => Rewrite (fun X => X) E I
).
Qed.

Definition L11 : ~(Eq True False) :=
    fun (E:Eq True False) => 
        Rewrite  (fun (X:Prop) => X) E I.

(* not canonical                                                                *)
Definition L12 : ~(Eq true false).
Proof.
    intros E. inversion E.
Qed.


Definition L13 : ~(Eq true false).
Proof.
    intros E. change ((fun (b:bool) => if b then True else False) false). 
    apply (Rewrite _ E). apply I.
Qed.

Definition L14: ~(Eq true false) :=
    fun (E:Eq true false) =>
        Rewrite (fun (b:bool) => if b then True else False) E I. 

Definition L15 : forall (n:nat), ~(Eq 0 (S n)).
Proof.
    intros n E. inversion E.
Qed.

Definition L16 : forall (n:nat), ~(Eq 0 (S n)).
Proof.
    intros n E. 
    change ((fun (m:nat) =>
        match m with
        | 0   => True
        | S _ => False
        end) (S n)).
    apply (Rewrite _ E).
    apply I.
Qed.

Definition L17 : forall (n:nat), ~(Eq 0 (S n)) :=
    fun (n:nat) =>
        fun (E:Eq 0 (S n)) =>
            Rewrite (fun (m:nat) =>
                match m with
                | 0     => True
                | S _   => False
                end) E I. 

Definition L18 : forall (m n:nat), Eq (S m) (S n) -> Eq m n.
Proof.
    intros m n E.
    change ((fun (x:nat) => 
        match x with
        | 0     => True
        | (S x) => Eq m x
        end) (S n)).
    apply (Rewrite _ E).
    exact (Refl m).
Qed.

Definition L19 : forall (m n:nat), Eq (S m) (S n) -> Eq m n :=
    fun (m n:nat) =>
        fun (E:Eq (S m) (S n)) =>
            Rewrite (fun (x:nat) =>
                match x with
                | 0     => True
                | (S x) => Eq m x
                end) E (Refl m).



