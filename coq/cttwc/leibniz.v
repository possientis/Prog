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

Lemma Rewrite' : forall (X:Type) (x y:X) (p:X -> Prop), 
    Eq X x y -> p x -> p y.
Proof.
    intros X x y p H H'. destruct H. assumption.
Qed.

Lemma EqInv3 : forall (X:Type) (x y:X), Eq X x y -> x = y.
Proof.
    intros X x y H. destruct H. reflexivity.
Qed.

(* Do it with 'refine' first ...                                               *)
Definition EqInv2 : forall (X:Type) (x y:X), Eq X x y -> x = y.
Proof. refine (
    fun (X:Type) =>
        fun (x y:X) =>
            fun (H:Eq X x y) =>
                match H with
                | Refl _ _  => eq_refl
                end

).
Defined.

Definition EqInv : forall (X:Type) (x y:X), Eq X x y -> x = y :=
    fun (X:Type) =>
        fun (x y:X) =>
            fun (H:Eq X x y) =>
                match H with
                | Refl _ _  => eq_refl
                end.


Print EqInv.

(* Do it with 'refine' first ...                                                *)
Definition Rewrite2 : forall (X:Type) (x y:X) (p:X -> Prop), 
    Eq X x y -> p x -> p y.
Proof. refine (
    fun (X:Type) =>
        fun(x y:X) =>
            fun (p:X -> Prop) =>
                fun (e:Eq X x y) =>
                        match e in (Eq _ x' y') return (p x' -> p y') with 
                        | Refl _ x' => fun (z:p x') => z
                        end
).
Defined.

Definition Rewrite : forall (X:Type) (x y:X) (p:X -> Prop), 
    Eq X x y -> p x -> p y 
    :=
    fun (X:Type) =>
        fun(x y:X) =>
            fun (p:X -> Prop) =>
                fun (e:Eq X x y) =>
                        match e with 
                        | Refl _ x' => fun (z:p x') => z
                        end.


