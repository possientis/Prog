(* using refine is very cool, feels like agda                                   *)

Require Extraction.

Extraction Language Haskell.

Definition eq_nat_dec : forall (n m:nat), {n = m} + {n <> m}.
    refine (fix f (n m:nat) : {n = m} + {n <> m} :=
        match n,m with
        | 0,0           => left _
        | S n, S m      => if f n m then left _ else right _
        | _, _          => right _
        end); congruence.
Defined.

(* Yes, this does work...                                                       *)
Definition S_not_O (n:nat) (p:S n = 0) : False :=
    match p with end.

Definition O_not_S (n:nat) (p:0 = S n) : False :=
    match p with end.

(* The ap function ...                                                          *)
Definition ap (a b:Type) (x y:a) (f:a -> b) (p:x = y) : f x = f y :=
    match p with
    | eq_refl _     => eq_refl _ 
    end.

Arguments ap {a} {b} {x} {y} _ _.

(* This feels a bit magical                                                     *)
Definition S_inj (n m:nat) (p:S n = S m) : n = m :=
    match p with
    | eq_refl _     => eq_refl _
    end.

Arguments S_inj {n} {m} _.

Definition eq_nat_dec3 : forall (n m:nat), {n = m} + {n <> m}.
    refine 
        (fix f (n m:nat) : {n = m} + {n <> m} :=
            match n as n' return {n' = m} + {n' <> m} with
            | 0     =>
                match m as m' return {0 = m'} + {0 <> m'} with
                | 0     => left  (eq_refl 0)
                | S m   => right (O_not_S m)
                end
            | S n   =>
                match m as m' return {S n = m'} + {S n <> m'} with
                | 0     => right (S_not_O n)
                | S m   => 
                    match f n m with
                    | left  p    => left  (ap S p)
                    | right p    => right (fun q => p (S_inj q))
                    end
                end
            end
        ).
Defined.

(* we can now remove the 'refine'                                               *)
Definition eq_nat_dec4 : forall (n m:nat), {n = m} + {n <> m} :=
    fix f (n m:nat) : {n = m} + {n <> m} :=
        match n as n' return {n' = m} + {n' <> m} with
        | 0     =>
            match m as m' return {0 = m'} + {0 <> m'} with
            | 0     => left  (eq_refl 0)
            | S m   => right (O_not_S m)
            end
        | S n   =>
            match m as m' return {S n = m'} + {S n <> m'} with
            | 0     => right (S_not_O n)
            | S m   => 
                match f n m with
                | left  p    => left  (ap S p)
                | right p    => right (fun q => p (S_inj q))
                end
            end
        end.

Fixpoint eq_nat_dec5 (n m:nat) : {n = m} + {n <> m} :=
    match n as n' return {n' = m} + {n' <> m} with
    | 0     =>
        match m as m' return {0 = m'} + {0 <> m'} with
        | 0     => left  (eq_refl 0)
        | S m   => right (O_not_S m)
        end
    | S n   =>
        match m as m' return {S n = m'} + {S n <> m'} with
        | 0     => right (S_not_O n)
        | S m   => 
            match eq_nat_dec5 n m with      (* <---- recursive call             *)
            | left  p    => left  (ap S p)
            | right p    => right (fun q => p (S_inj q))
            end
        end
    end.

(*
Extraction eq_nat_dec5.
*)



