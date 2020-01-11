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

Definition vecDes (a:Type)
    (P:forall (n:nat), Vec n a -> Prop)
    (H0: P 0 Nil)
    (H1: forall (n:nat) (xs:Vec (S n) a), P (S n) xs)
    (n:nat)
    (xs:Vec n a)
    : P n xs :=
    match xs with
    | Nil       => H0
    | Cons x ys => H1 _ _
    end.


Arguments vecInd {a}.

Definition cast (a:Type) (n m:nat) (p:n = m) (xs:Vec n a) : Vec m a :=
    match p with
    | eq_refl _ => xs
    end.

Arguments cast {a} {n} {m}.

Notation "x ++ y" := (append x y) (at level 60, right associativity).

Axiom irrelevance : forall (A:Prop) (p q:A), p = q.

Arguments irrelevance {A}.

Lemma Cons_cast : forall (a:Type)(n m:nat)(x:a)(xs:Vec n a)(p:n = m)(q:S n = S m),
    Cons x (cast p xs) = cast q (Cons x xs).
Proof.
    intros a n m x xs p q. destruct p. simpl.
    rewrite (irrelevance q (eq_refl _)). reflexivity.
Qed.

Lemma append_assoc : 
    forall (a:Type) (n m p:nat) (xs:Vec n a) (ys:Vec m a) (zs:Vec p a),
        (xs ++ ys) ++ zs = cast (plus_assoc n m p) (xs ++ (ys ++ zs)).
Proof.
    intros a n m p xs ys. revert p. revert ys. revert m.
    apply (vecInd (fun (n:nat) (xs:Vec n a) => forall m ys p zs, 
        (xs ++ ys) ++ zs = cast (plus_assoc n m p) (xs ++ (ys ++ zs)))).
    - intros m ys p zs. 
      rewrite (irrelevance (plus_assoc 0 m p) (eq_refl _)). reflexivity.
    - clear n xs. intros n x xs. intros IH. 
      intros m ys p zs. simpl. rewrite IH.
      remember (plus_assoc n m p) as p1 eqn:E1.
      remember (plus_assoc (S n) m p) as p2 eqn:E2.
      rewrite (Cons_cast _ _ _ _ _ p1 p2). 
      reflexivity.
Qed.

Definition P1 (a:Type) (n:nat) (xs:Vec n a) : Prop :=
    (match n return Vec n a -> Prop with
     | 0        =>  fun _ => True
     | (S p)    =>  fun xs => exists (ys:Vec p a) (x:a), xs = Cons x ys
     end) xs.

Arguments P1 {a}.

Lemma L1 : forall (a:Type) (n:nat) (xs:Vec n a), P1 n xs.
Proof.
    intros a n. destruct xs as [|n x xs].
    - unfold P1. apply I.
    - unfold P1. exists xs. exists x. reflexivity.
Qed.


(*
Lemma L2 : forall (a:Type) (n:nat) (xs:Vec (S n) a),
    exists (ys:Vec n a) (x:a), xs = Cons x ys.
Proof.
    intros a n.

Show.
*)

