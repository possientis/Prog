(* These proofs are normal: no further reduction is possible                    *)

Definition L1 (X:Prop)   : X -> X      := fun x => x.
Definition L2 (X Y:Prop) : X -> Y -> X := fun x y => x.
Definition L3 (X Y:Prop) : X -> Y -> Y := fun x y => y.

Definition L4 (X Y Z:Prop) : (X -> Y -> Z) -> (Y -> X -> Z) := fun f y x => f x y.
Definition L5 (X Y:Prop) : X -> Y -> X /\ Y := fun x y => conj x y.

Definition L6 (X Y:Prop) : X /\ Y -> X := fun p => match p with conj x y => x end.
Definition L7 (X Y:Prop) : X /\ Y -> Y := fun p => match p with conj x y => y end.
Definition L8 (X Y:Prop) : X /\ Y -> Y /\ X := fun p => match p with conj x y => conj y x end.
Definition L9 (X Y:Prop) : X -> X \/ Y := @or_introl X Y.
Definition L10 (X Y:Prop): Y -> X \/ Y := @or_intror X Y.
Definition L11 (X Y:Prop): X \/ Y -> Y \/ X := fun p =>
    match p with 
    | or_introl x => or_intror x 
    | or_intror y => or_introl y
    end.

(* Nested pattern matching is a notational convenience and can be desugared     *)
Definition L12 (X Y Z:Prop): (X /\ Y) /\ Z -> X /\ (Y /\ Z) := fun p =>
    match p with
    | conj (conj x y) z => conj x (conj y z)
    end.


Definition L13 (X Y Z:Prop): (X /\ Y) /\ Z -> X /\ (Y /\ Z) := fun p =>
    match p with
    | conj xy z =>
        match xy with
        | conj x y => conj x (conj y z)
        end
    end. 
