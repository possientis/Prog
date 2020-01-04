Require Import Plus.

Inductive Vec_ (a:Type) : nat -> Type :=
| Nil   : Vec_ a 0
| Cons  : forall (n:nat), a -> Vec_ a n -> Vec_ a (S n)
.

Definition Vec (n:nat) (a:Type) : Type := Vec_ a n.

Arguments Nil {a}.
Arguments Cons {a} {n}.

Definition v1 : Vec 3 nat := Cons 0 (Cons 1 (Cons 2 Nil)).
Definition v2 : Vec 2 nat := Cons 3 (Cons 4 Nil).


Fixpoint append (a:Type) (n m:nat) (xs:Vec n a) (ys:Vec m a) : Vec (n + m) a :=
    match xs with
    | Nil          => ys
    | Cons x xs    => Cons x (append _ _ _ xs ys)
    end.

Arguments append {a} {n} {m}.

Definition v3 : Vec 5 nat := append v1 v2.

Fixpoint vecInd (a:Type) 
    (P:forall (n:nat), Vec n a -> Prop) 
    (H0:P 0 Nil)
    (IH:forall (n:nat) (x:a) (xs:Vec n a), P n xs -> P (S n) (Cons x xs))
    (n:nat) 
    (xs:Vec n a)
    : P n xs :=
    match xs with 
    | Nil       => H0
    | Cons x ys => IH _ x ys (vecInd a P H0 IH _ ys)
    end
    .

Definition cast (a:Type) (n m:nat) (p:n = m) (xs:Vec n a) : Vec m a :=
    match p with
    | eq_refl _ => xs
    end.

Arguments cast {a} {n} {m}.

(*
Lemma append_assoc : forall (a:Type) (n m p:nat) (xs:Vec n a) (ys:Vec m a) (zs:Vec p a),
    append (append xs ys) zs = cast (plus_assoc n m p) (append xs (append ys zs)).
Proof.

Show.
*)
