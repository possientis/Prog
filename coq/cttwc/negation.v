Definition L1 (X:Prop) : X -> ~(~ X) := fun x f => f x.

Definition L2 (X Y:Prop) : X -> ~X -> Y := fun x f => match (f x) with end.

Definition L3 (X Y:Prop) : (X -> Y) -> (~Y -> ~X) := fun f g x => g (f x).

Definition L4 (X:Prop) : ~X -> ~~~X := fun f g => g f. 

Definition L5 (X:Prop) : ~~~X -> ~X := fun f x => f (fun g => g x).

Definition L6 (X:Prop) : ~~X -> (X -> ~X) -> False := 
    fun f g => f (fun x => g x x). 

(* Using let, not a normal proof                                                *)
Definition L7 (X:Prop) : (X -> ~X) -> (~X -> X) -> False :=
    fun f g => let h := fun x => f x x in f (g h) (g h).

Definition L8 (X:Prop) : False -> X :=
    fun (p:False) => match p with end.


Definition L9 : ~False := fun x => x.

Definition L10 : ~~False <-> False := conj
    (fun f => f (fun x => x))
    (fun (p:False) => match p with end).

Definition L11 : ~~True <-> True := conj
    (fun _ => I)
    (fun _ => (fun g => g I)).

Definition L12 (X:Prop) : ~~~X <-> ~X := conj
    (fun f => fun x => f (fun g => g x))
    (fun f => fun g => g f).

(* with type annotations                                                        *)
Definition L13 (X Y:Prop) : (X -> ~~Y) <-> (~Y -> ~X) := conj
    (fun (f:X -> ~~Y) => fun (g:~Y) => fun (x:X) => f x g)
    (fun (f:~Y -> ~X) => fun (x:X) => fun (g:~Y) => f g x).

(* not using let binding to have normal proof                                   *)
Definition L14 (X:Prop) : ~(X <-> ~X) := 
    fun p => 
        match p with
        | conj f (* : X -> ~X *) g (* : ~X -> X *)  =>
            f (g (fun x => f x x)) (g (fun x => f x x))
        end.

Definition L15 (X Y:Prop) : ~(X \/ Y) <-> ~X /\ ~Y := conj
    (fun (f : ~(X \/ Y)) => conj
        (fun (x:X) => f (or_introl x))
        (fun (y:Y) => f (or_intror y)))
    (fun (p : ~X /\ ~Y) => 
        match p with
        | conj f g  =>
            fun (q:X \/ Y) =>
                match q with
                | or_introl x   => f x
                | or_intror y   => g y
                end
        end).
        





