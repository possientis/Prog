Class Eq (a : Type) : Type :=
    { equal : a -> a -> Prop 
    ; refl  : forall (x:a), equal x x 
    ; sym   : forall (x y:a), equal x y -> equal y x
    ; trans : forall (x y z:a), equal x y -> equal y z -> equal x z 
    }.

(*
Instance defaultEq (a:Type) : Eq a :=
    { equal := fun (x y:a)                      => x = y
    ; refl  := fun (x:a)                        => eq_refl x
    ; sym   := fun (x y:a) (p:x=y)              => eq_sym p
    ; trans := fun (x y z:a) (p:x=y) (q:y=z)    => eq_trans p q
    }.
*)

Definition notEqual (a:Type) (_:Eq a) (x y:a) : Prop := ~ equal x y.

Definition prodEqual (a b:Type) (_:Eq a) (_:Eq b) (p q:a * b) : Prop :=
    match p with
    | (x,y) =>
        match q with
        | (x',y') => equal x x' /\ equal y y'
        end
    end.

Arguments prodEqual {a} {b}.

Lemma prodRefl : forall (a b:Type) (e:Eq a) (e':Eq b) (p:a * b), 
    prodEqual _ _ p p.
Proof.
    intros a b e e' p. destruct p as (x,y). unfold prodEqual. split; apply refl.
Qed.


(*
Instance prodEq (a b:Type) (_:Eq a) (_:Eq b) : Eq (a * b) :=
    { equal := prodEqual _ _
    ; refl  := _
    ; sym   := _
    ; trans := _
    }.
*)
