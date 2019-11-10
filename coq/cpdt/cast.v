Definition cast (a b:Set) (p:a = b) (x:a) : b :=
    match p with
    | eq_refl       => x
    end.
