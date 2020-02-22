Check @conj.        (* : forall A B : Prop, A -> B -> A /\ B                    *)
Check @or_introl.   (* : forall A B : Prop, A -> A \/ B                         *) 
Check @or_intror.   (* : forall A B : Prop, B -> A \/ B                         *) 


(* Impredicative : Quantifying over Prop                                        *)

(* The following equivalences show that False, /\, \/ can be defined using      *)
(* only dependent function types.                                               *)

(* Impredicative characterization of falsity                                    *)
Definition L1 : False <-> forall (Z:Prop), Z := conj
    (fun (p:False) => match p with end)
    (fun f => f False).

(* Impredicative characterization of conjonction                                *)
Definition L2 (X Y:Prop) : X /\ Y <-> forall (Z:Prop), (X -> Y -> Z) -> Z := conj
    (fun p =>
        match p with
        | conj x y  =>
            fun Z => 
                fun f => f x y
        end)
    (fun f => conj
        (f X (fun x y => x))
        (f Y (fun x y => y))).

(* Impredicative characterization of disjunction                                *)
Definition L3 (X Y:Prop) : 
    X \/ Y <-> forall (Z:Prop), (X -> Z)->(Y -> Z)->Z := conj
        (fun (p : X \/ Y)   =>
            match p with
            | or_introl x   =>
                fun (Z:Prop)    => 
                    fun (f:X -> Z) (g:Y -> Z) => f x
            | or_intror y   =>
                fun (Z:Prop) =>
                    fun (f:X -> Z) (g:Y -> Z) => g y
            end)
        (fun (f: forall (Z:Prop), (X -> Z) -> (Y -> Z) -> Z) => 
            f (X \/ Y) (fun x => or_introl x) (fun y => or_intror y)).
            


Definition L4 : True <-> forall (Z:Prop), Z -> Z := conj
    ( fun _ => fun Z => fun z => z)
    ( fun _ => I).


Definition L5 (X Y:Prop) (p:X -> Y -> Prop) : 
    (forall (x:X) (y:Y), p x y) <-> (forall (y:Y) (x:X), p x y) := conj
        (fun f => fun y => fun x => f x y)
        (fun f => fun x => fun y => f y x).
