Class Eq (a : Type) : Type :=
    { equal : a -> a -> Prop 
    ; refl  : forall (x:a), equal x x 
    ; sym   : forall (x y:a), equal x y -> equal y x
    ; trans : forall (x y z:a), equal x y -> equal y z -> equal x z 
    }.

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

Arguments prodRefl {a} {b}.

Lemma prodSym : forall (a b:Type) (e:Eq a) (e':Eq b) (p q:a * b),
    prodEqual _ _ p q -> prodEqual _ _ q p.
Proof.
    intros a b e e' p q. destruct p as (x,x'), q as (y,y'). simpl.
    intros [H H']. split; apply sym; assumption.
Qed.

Arguments prodSym {a} {b}.

Lemma prodTrans : forall (a b:Type) (e:Eq a) (e':Eq b) (p q r:a * b),
    prodEqual _ _ p q -> prodEqual _ _ q r -> prodEqual _ _ p r.
Proof.
    intros a  b e e' p q r. destruct p as (x,x'), q as (y,y'), r as (z,z'). simpl.
    intros [H H'] [I I']. split.
    - apply trans with y;  assumption.
    - apply trans with y'; assumption.
Qed.

Arguments prodTrans {a} {b}.

Instance prodEq (a b:Type) (_:Eq a) (_:Eq b) : Eq (a * b) :=
    { equal := prodEqual _ _
    ; refl  := prodRefl _ _
    ; sym   := prodSym _ _ 
    ; trans := prodTrans _ _
    }.


Instance defaultEq (a:Type) : Eq a :=
    { equal := fun (x y:a)                      => x = y
    ; refl  := fun (x:a)                        => eq_refl x
    ; sym   := fun (x y:a) (p:x=y)              => eq_sym p
    ; trans := fun (x y z:a) (p:x=y) (q:y=z)    => eq_trans p q
    }.

Class Ord (a :Type) (e:Eq a) : Type :=
    { le     : a -> a -> Prop
    ; cong   : forall (x x' y y':a), equal x x' -> equal y y' -> le x y -> le x' y'
    ; refl'  : forall (x:a), le x x
    ; trans' : forall (x y z:a), le x y -> le y z -> le x z
    }.



