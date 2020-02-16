Definition L1 (X:Prop) : X -> ~(~ X) := fun x f => f x.

Definition L2 (X Y:Prop) : X -> ~X -> Y := fun x f => match (f x) with end.

Definition L3 (X Y:Prop) : (X -> Y) -> (~Y -> ~X) := fun f g x => g (f x).

Definition L4 (X:Prop) : ~X -> ~~~X := fun f g => g f. 

Definition L5 (X:Prop) : ~~~X -> ~X := fun f x => f (fun g => g x).

Definition L6 (X:Prop) : ~~X -> (X -> ~X) -> False := 
    fun f g => f (fun x => g x x). 

Definition L7 (X:Prop) : (X -> ~X) -> (~X -> X) -> False :=
    fun f g => let h := fun x => f x x in f (g h) (g h).
