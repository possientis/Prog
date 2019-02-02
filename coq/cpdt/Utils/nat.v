Fixpoint blt_nat (n m:nat) : bool :=
    match n with
    | 0 => 
        match m with
        | 0     => false
        | S _   => true
        end
    | S n'  =>
        match m with
        | 0     => false
        | S m'  => blt_nat n' m'
        end
    end.


