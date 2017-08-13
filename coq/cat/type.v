Require Import Axiom_Type_Equality.

Record Arrow : Type := arrow
    {   dom  : Set
    ;   cod  : Set
    ;   arr  : dom -> cod
    }
    .

Definition id (a : Set) : Arrow := arrow a a (fun x => x).

Definition domain (f:Arrow) : Arrow := id (dom f).
Definition codomain (f:Arrow) : Arrow := id (cod f). 


Definition compose (f g: Arrow) : option Arrow :=
    match f with
        | arrow a b f' => 
            match g with
                | arrow b' c g' =>

                    end
            end
    end.
    

