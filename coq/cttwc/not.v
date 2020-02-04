Definition not := fun (x : bool) => 
    match x with 
    | true => false 
    | false => true 
    end.

Definition plus := fix g (x:nat) : nat -> nat := 
    fun (y:nat) =>
        match x with
        | 0     => y
        | S x'  => S (g x' y)
        end. 
