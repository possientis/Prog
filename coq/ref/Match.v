Inductive Bool : Type := 
| True  : Bool 
| False : Bool
. 

Inductive Eq (a:Type) (x:a) : a -> Prop := 
| refl : Eq a x x
.

Arguments Eq {a}.
Arguments refl {a}.

Inductive Or (A:Prop) (B:Prop) : Prop :=
| Left  : A -> Or A B
| Right : B -> Or A B
.

Arguments Left  {A} {B}.
Arguments Right {A} {B}.

Definition boolDec (b:Bool) : Or (Eq b True) (Eq b False) :=
    match b with
    | True  => Left  (refl True)
    | False => Right (refl False) 
    end.

Compute boolDec True.
Compute boolDec False.

Definition boolDec' (b:Bool) : Or (Eq b True) (Eq b False) :=
    match b return Or (Eq b True) (Eq b False) with
    | True  => Left  (refl True)
    | False => Right (refl False) 
    end.

Compute boolDec' True.
Compute boolDec' False.

Definition boolDec'' (b:Bool) : Or (Eq b True) (Eq b False) :=
    match b as x return Or (Eq x True) (Eq x False) with
    | True  => Left  (refl True)
    | False => Right (refl False) 
    end.

Compute boolDec'' True.
Compute boolDec'' False.

Definition Eq_sym (a:Type) (x y:a) (H:Eq x y) : Eq y x :=
    match H with
    | refl _    => refl _
    end.

Lemma L1 : forall (a:Type) (x y:a), Eq x y -> Eq y x.
Proof.
    intros a x y H. apply Eq_sym. assumption. 
Qed.
