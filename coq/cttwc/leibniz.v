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

Inductive Eq2 (X:Type) : X -> X -> Prop :=
| Refl2 : forall (x:X), Eq2 X x x
.

Arguments Eq2 {X}.

Arguments Refl2 {X}.


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
Definition Rewrite'' : forall (X:Type) (x y:X) (p:X -> Prop), 
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

Definition Rewrite2 : forall (X:Type) (x y:X) (p:X -> Prop), 
    Eq2 x y -> p x -> p y 
    :=
    fun (X:Type) =>
        fun(x y:X) =>
            fun (p:X -> Prop) =>
                fun (e:Eq2 x y) =>
                        match e with 
                        | Refl2 x' => fun (z:p x') => z
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


Definition L20 : forall (X Y:Type) (f:X -> Y) (x y:X), Eq x y -> Eq (f x) (f y).
Proof.
    intros X Y f x y E.
    change ((fun (z:X) => Eq (f x) (f z)) y).
    apply (Rewrite _ E).
    exact (Refl (f x)).
Qed.

Definition L21 : forall (X Y:Type) (f:X -> Y) (x y:X), Eq x y -> Eq (f x) (f y) :=
    fun (X Y:Type) =>
        fun (f:X -> Y) =>
            fun (x y:X) =>
                fun (E:Eq x y) =>
                    Rewrite (fun (z:X) => Eq (f x) (f z)) E (Refl (f x)).

Definition L22 : forall (X:Type) (x y:X), Eq x y -> Eq y x.
Proof.
    intros X x y E.
    change ((fun (z:X) => Eq z x) y).
    apply (Rewrite _ E).
    exact (Refl x).
Qed.

Definition L23 : forall (X:Type) (x y:X), Eq x y -> Eq y x :=
    fun (X:Type) =>
        fun (x y:X) =>
            fun (E:Eq x y) =>
                Rewrite (fun (z:X) => Eq z x) E (Refl x).

Definition L24 : forall (X:Type) (x y z:X), Eq x y -> Eq y z -> Eq x z.
Proof.
    intros X x y z Exy Eyz.
    change ((fun (u:X) => Eq x u) z).
    apply (Rewrite _ Eyz).
    exact Exy.
Qed.


Definition L25 : forall (X:Type) (x y z:X), Eq x y -> Eq y z -> Eq x z :=
    fun (X:Type) =>
        fun (x y z:X) =>
            fun (Exy:Eq x y) =>
                fun (Eyz:Eq y z) =>
                    Rewrite (fun (u:X) => Eq x u) Eyz Exy.

(* All these equalities are equivalent                                          *)
Definition L26 : forall (X:Type) (x y:X), Eq x y -> Eq2 x y.
Proof.
    intros X x y E.
    change ((fun (z:X) => Eq2 x z) y).
    apply (Rewrite _ E).
    exact (Refl2 x).
Qed.

Definition L27 : forall (X:Type) (x y:X), Eq x y -> Eq2 x y :=
    fun (X:Type) =>
        fun (x y:X) =>
            fun (E:Eq x y) =>
                Rewrite (fun (z:X) => Eq2 x z) E (Refl2 x).


Variable a : Type.
Variable (x y : a).
Variable plus : a -> a -> a.

Notation "u $ v" := (plus u v) (at level 20, left associativity).

(* The term y $ x cannot be rewritten in t, as $ is left associative            *)
Definition t:Prop := x $ y $ x = y.

Definition p1 (u:a) : Prop := u $ y $ x = y.

Definition L28 : p1 x = t := eq_refl _.

Definition p2 (u:a) : Prop := x $ y $ x = u.

Definition L29 : p2 y = t := eq_refl _.

Definition p3 (u:a) : Prop := x $ u $ x = u.

Definition L30 : p3 y = t := eq_refl _.

Definition p4 (u:a) : Prop := u $ x = y.

Definition L31 : p4 (x $ y) = t := eq_refl _.

Definition L32 : forall (n:nat), ~Eq 0 (S n).
Proof.
    intros n E.
    change ((fun (n:nat) => 
        match n with 
        | 0     => True
        | S_    => False
        end) (S n)).
    apply (Rewrite _ E).
    apply I.
Qed.

Definition L33 : forall (n:nat), ~Eq 0 (S n) :=
    fun (n:nat) =>
        fun (E:Eq 0 (S n)) =>
            Rewrite (fun (m:nat) =>
                match m with
                | 0     => True
                | S _   => False
                end) E I.


Definition Eq3 : forall (X:Type), X -> X -> Prop :=
    fun (X:Type) =>
        fun (x y:X) =>
            forall (p:X -> Prop), p x -> p y.

Arguments Eq3 {X}.

Definition Refl3 : forall (X:Type) (x:X), Eq3 x x :=
    fun (X:Type) =>
        fun (x:X) =>
            fun (p:X -> Prop) =>
                fun (z:p x) => z.

Arguments Refl3 {X}.


Definition Rewrite3 : forall (X:Type) (x y:X) (p:X -> Prop), 
    Eq3 x y -> p x -> p y :=
    fun (X:Type) =>
        fun (x y:X) =>
            fun (p:X -> Prop) =>
                fun (E:Eq3 x y) =>
                    fun (z:p x) => E p z.


Definition L34 : forall (X Y Z:Prop), X /\ Y -> (X -> Y -> Z) -> Z :=
    fun (X Y Z:Prop) =>
        fun (p:X /\ Y) =>
            fun (f:X -> Y -> Z) =>
                match p with
                | conj x y  => f x y
                end.

Definition L35 : forall (X Y Z:Prop), X \/ Y -> (X -> Z) -> (Y -> Z) -> Z :=
    fun (X Y Z:Prop) =>
        fun (p:X \/ Y) =>
            fun (px:X -> Z) =>
                fun (py:Y -> Z) =>
                    match p with
                    | or_introl x   => px x
                    | or_intror y   => py y
                    end.

(* Impredicative definitions, not using inductive type definition               *)
Definition And (X Y:Prop) : Prop := forall (Z:Prop), (X -> Y -> Z) -> Z. 

Definition Or (X Y:Prop) : Prop := forall (Z:Prop), (X -> Z) -> (Y -> Z) -> Z.

(* inductive and impredicative definitions of conjunction are equivalent        *)
Definition L36 : forall (X Y:Prop), And X Y <-> X /\ Y :=
    fun (X Y:Prop) => conj
        (fun (f:forall (Z:Prop), (X -> Y -> Z) -> Z) => conj
            (f X (fun (x:X) (y:Y) => x))
            (f Y (fun (x:X) (y:Y) => y)))
        (fun (p:X /\ Y) =>
            fun (Z:Prop) =>
                fun (f:X -> Y -> Z) =>
                    match p with
                    | conj x y => f x y
                    end).

(* Inductive and impredicative definitions of disjunction are equivalent        *)
Definition L37 : forall (X Y:Prop), Or X Y <-> X \/ Y :=
    fun (X Y:Prop) => conj
        (fun (f:forall (Z:Prop), (X -> Z) -> (Y -> Z) -> Z) =>
           f (X \/ Y) (fun (x:X) => or_introl x) (fun (y:Y) => or_intror y))
        (fun (p:X \/ Y) =>
            fun (Z:Prop) =>
                fun (f:X -> Z) =>
                    fun (g:Y-> Z) =>
                        match p with
                        | or_introl x   => f x
                        | or_intror y   => g y
                        end). 

(* Constructor for conjonction based on impredicative definition.               *)
Definition AndI : forall (X Y:Prop), X -> Y -> And X Y :=
    fun (X Y:Prop) =>
        fun (x:X) =>
            fun (y:Y) =>
                fun (Z:Prop) =>
                    fun (f:X -> Y -> Z) => f x y.

(* Destructor for conjonction based on impredicative definition.                *)
Definition AndE : forall (X Y Z:Prop), And X Y -> (X -> Y -> Z) -> Z :=
    fun (X Y Z:Prop) =>
        fun (f:And X Y) =>
            fun (g:X -> Y -> Z) =>
                f Z g. 

Definition OrI1 : forall (X Y:Prop), X -> Or X Y :=
    fun (X Y:Prop) =>
        fun (x:X) =>
            fun (Z:Prop) =>
                fun(f:X -> Z) =>
                    fun (g:Y -> Z) => f x.  
     

Definition OrI2 : forall (X Y:Prop), Y -> Or X Y :=
    fun (X Y:Prop) =>
        fun (y:Y) =>
            fun (Z:Prop) =>
                fun(f:X -> Z) =>
                    fun (g:Y -> Z) => g y.  
     

Definition OrE : forall (X Y Z:Prop), Or X Y -> (X -> Z) -> (Y -> Z) -> Z :=
    fun (X Y Z:Prop) =>
        fun (p:Or X Y) =>
            fun (f:X -> Z) =>
                fun (g:Y -> Z) =>
                    p Z f g.

