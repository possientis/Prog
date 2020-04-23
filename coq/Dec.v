Inductive Dec (p:Prop) : Type :=
| isTrue : p  -> Dec p
| isFalse: ~p -> Dec p
.

Arguments isTrue {p}.
Arguments isFalse {p}.

Class Decidable (p:Prop) := { dec : Dec p }.
 
Definition ite (a:Type) (p:Prop) (d:Decidable p) (x y:a) : a :=
    if dec then x else y.

Arguments ite {a} {p}.

Instance decTrue   : Decidable True   := { dec := isTrue I  }.
Instance decFalse  : Decidable False  := { dec := isFalse (fun x => x) }.

Instance decNot (p:Prop) (d:Decidable p) : Decidable (~p) := { dec := 
    match dec with
    | isTrue q  => isFalse (fun f => f q)
    | isFalse q => isTrue q
    end 
}.

Definition check (p:Prop) (d:Decidable p) : bool :=
    if dec then true else false.

Definition L1 : check True _ = true.
Proof. reflexivity. Qed.

Definition L2 : check False _ = false.
Proof. reflexivity. Qed.

Instance decImp (p q:Prop) (d1:Decidable p) (d2:Decidable q) : Decidable (p -> q)
    := { dec := 
            match dec with
            | isTrue y  => isTrue (fun _ => y)
            | isFalse y =>
                match dec with
                | isTrue x  => isFalse (fun f => y (f x))
                | isFalse x => isTrue  (fun z => match x z with end)
                end
            end
}.  

Compute check (False -> False) _.
Compute check (False -> True) _.
Compute check (True -> True) _.
Compute check (True -> False) _.
Compute check ((True -> False) -> False) _.

