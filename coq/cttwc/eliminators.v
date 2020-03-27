
Definition BoolE : forall (p:bool -> Prop), p true -> p false -> forall (x:bool), p x :=
    fun (p:bool -> Prop) => 
        fun (tt:p true) =>
            fun (ff: p false) =>
                fun (x:bool) =>
                    match x with
                    | true  => tt
                    | false => ff
                    end.

Definition BoolC1 : bool := true.
Definition BoolC2 : bool := false.

Definition L1 : forall (x:bool), negb (negb x) = x.
Proof.
    intros x.
    apply (BoolE (fun z => negb (negb z) = z)).
    - exact (eq_refl true).
    - exact (eq_refl false).
Qed.


Definition L2 : forall (x:bool), negb (negb x) = x :=
    fun (x:bool) => BoolE 
        (fun (z:bool) => negb (negb z) = z) 
        (eq_refl true) 
        (eq_refl false) 
        x.


Definition BoolRec : forall (p:bool -> Type), p true -> p false -> forall (x:bool), p x :=
    fun (p:bool -> Type) => 
        fun (tt:p true) =>
            fun (ff: p false) =>
                fun (x:bool) =>
                    match x with
                    | true  => tt
                    | false => ff
                    end.

Definition not : bool -> bool := BoolRec (fun (x:bool) => bool) false true.


Definition L3 : not = fun(x:bool) => match x with true => false | false => true end :=
    eq_refl not.

Definition BoolE' : forall (p:bool -> Prop), p true -> p false -> forall (x:bool), p x :=
    fun (p:bool -> Prop) => BoolRec p.
    
Variable BoolE1 : forall (p:bool -> Prop), p true -> p false -> forall (x:bool), p x.

Definition L4 : forall (x:bool), x = true \/ x = false :=
    fun (x:bool) =>
        match x with
        | true  => or_introl (eq_refl true)
        | false => or_intror (eq_refl false)
        end.

Definition L5 : forall (x:bool), x = true \/ x = false := BoolE1 
    (fun (x:bool) => x = true \/ x = false) 
    (or_introl (eq_refl true))
    (or_intror (eq_refl false)).

Definition L6 : forall (p:bool -> Prop), (forall (x y:bool), y = x -> p x) -> forall (x:bool), p x :=
    fun (p:bool -> Prop) => 
        fun (q:forall (x y:bool), y = x -> p x) =>
            fun (x:bool) => q x x (eq_refl x).


Fail Definition L7 : forall (p:bool -> Prop) (x:bool), (x = true -> p true) -> (x = false -> p false) -> p x :=
    fun (p:bool -> Prop) =>
        fun (x:bool) =>
            fun (tt:x = true -> p true) =>
                fun (ff:x = false -> p false) =>
                    match x with
                    | true  => tt (eq_refl true)
                    | false => ff (eq_refl false)
                    end.

Definition bool_dec : forall (x:bool), x = true \/ x = false :=
    fun (x:bool) =>
        match x with
        | true  => or_introl (eq_refl true)
        | false => or_intror (eq_refl false)
        end.

Fail Definition L8 : forall (p:bool -> Prop) (x:bool), (x = true -> p true) -> (x = false -> p false) -> p x :=
    fun (p:bool -> Prop) =>
        fun (x:bool) =>
            fun (tt:x = true -> p true) =>
                fun (ff:x = false -> p false) =>
                    match bool_dec x with
                    | or_introl p  => tt p
                    | or_intror p  => ff p
                    end.

Definition bool_dec' : forall (x:bool), {x = true} + {x = false} :=
    fun (x:bool) => 
        match x with
        | true  => left  (eq_refl true)
        | false => right (eq_refl false)
        end. 


Fail Definition L9 : forall (p:bool -> Prop) (x:bool), (x = true -> p true) -> (x = false -> p false) -> p x :=
    fun (p:bool -> Prop) =>
        fun (x:bool) =>
            fun (tt:x = true -> p true) =>
                fun (ff:x = false -> p false) =>
                    match bool_dec' x with
                    | left p   => tt p
                    | right p  => ff p
                    end.


Definition L10 : forall (p:bool -> Prop) (x:bool), (x = true -> p true) -> (x = false -> p false) -> p x :=
    fun (p:bool -> Prop) =>
        fun (x:bool) =>
            fun (tt:x = true -> p true) =>
                fun (ff:x = false -> p false) =>
                    match bool_dec x with
                    | or_introl p  => tt p
                    | or_intror p  => ff p
                    end.


