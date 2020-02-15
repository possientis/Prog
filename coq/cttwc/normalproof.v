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

Definition L14 (X Y:Prop) : X /\ Y <-> Y /\ X := conj
    (fun p => match p with conj x y => conj y x end)
    (fun p => match p with conj y x => conj x y end).

Definition L15 (X Y Z:Prop) : X /\ (Y /\ Z) <-> (X /\ Y) /\ Z := conj
    (fun p => match p with conj x (conj y z) => conj (conj x y) z end)
    (fun p => match p with conj (conj x y) z => conj x (conj y z) end).

Definition L16 (X Y Z:Prop) : X /\ (Y \/ Z) <-> X /\ Y \/ X /\ Z := conj
    (fun p => 
        match p with conj x yz => 
            match yz with
            | or_introl y   => or_introl (conj x y)
            | or_intror z   => or_intror (conj x z)
            end
        end)
    (fun p =>
        match p with
        | or_introl (conj x y)  => conj x (or_introl y)
        | or_intror (conj x z)  => conj x (or_intror z)
        end).

Definition L17 (X Y:Prop) : X /\ (X \/ Y) <-> X := conj
    (fun p => match p with conj x _ => x end)
    (fun x => conj x (or_introl x)).


Definition L18 (X Y:Prop) : X \/ Y <-> Y \/ X := conj
    (fun p => match p with
        | or_introl x   => or_intror x
        | or_intror y   => or_introl y
        end)
    (fun p => match p with
        | or_introl y   => or_intror y
        | or_intror x   => or_introl x
        end). 

Definition L19 (X Y Z:Prop) : X \/ (Y \/ Z) <-> (X \/ Y) \/ Z := conj
    (fun p =>
        match p with 
        | or_introl x   => or_introl (or_introl x)
        | or_intror q   =>
            match q with
            | or_introl y   => or_introl (or_intror y)
            | or_intror z   => or_intror z
            end
        end)
    (fun p =>
        match p with 
        | or_introl q =>
            match q with
            | or_introl x   => or_introl x
            | or_intror y   => or_intror (or_introl y)
            end
        | or_intror z       => or_intror (or_intror z)
        end).

Definition L20 (X Y Z:Prop) : X \/ (Y /\ Z) <-> (X \/ Y) /\ (X \/ Z) := conj
    (fun p => match p with
        | or_introl x           => conj (or_introl x) (or_introl x)
        | or_intror (conj y z)  => conj (or_intror y) (or_intror z)
        end)
    (fun p => 
        match p with conj py pz =>
            match py with
            | or_introl x   => or_introl x
            | or_intror y   =>
                match pz with
                | or_introl x => or_introl x
                | or_intror z => or_intror (conj y z)
                end
            end
        end).

Definition L21 (X Y:Prop) : X \/ (X /\ Y) <-> X := conj
    (fun p  =>
        match p with
        | or_introl x           => x
        | or_intror (conj x y)  => x
        end)
    (fun x => or_introl x).
        
