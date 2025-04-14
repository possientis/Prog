Print prod.

(*
Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B
*)

Print and.

(*
Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B
*)


Definition toProd (A B:Prop) (p:and A B) : prod A B :=
    match p with
    | conj x y      => (x,y)
    end.

Arguments toProd {A} {B} _.

Definition toAnd (A B:Prop) (p:prod A B) : and A B :=
    match p with
    | (x,y)   => conj x y
    end.

Arguments toAnd {A} {B} _.

Lemma check1: forall (A B:Prop) (p:and A B), toAnd (toProd p) = p.
Proof. intros A B p. destruct p. reflexivity. Qed.

Lemma check2: forall (A B:Prop) (p:prod A B), toProd (toAnd p) = p.
Proof. intros A B p. destruct p. reflexivity. Qed.

