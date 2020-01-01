Inductive Vec : nat -> Type -> Type :=
| Nil   : forall (a:Type), Vec 0 a
| Cons  : forall (n:nat) (a:Type), a -> Vec n a -> Vec (S n) a
.

Arguments Nil {a}.
Arguments Cons {n} {a}.

Definition v1 : Vec 3 nat := Cons 0 (Cons 1 (Cons 2 Nil)).
Definition v2 : Vec 2 nat := Cons 3 (Cons 4 Nil).

Inductive Vec' (a:Type) : nat -> Type :=
| Nil'   : Vec' a 0
| Cons'  : forall (n:nat), a -> Vec' a n -> Vec' a (S n)
.

Arguments Nil' {a}.
Arguments Cons' {a} {n}.

Definition v1' : Vec' nat 3 := Cons' 0 (Cons' 1 (Cons' 2 Nil')).
Definition v2' : Vec' nat 2 := Cons' 3 (Cons' 4 Nil').

Fixpoint append (a:Type) (n m:nat) (xs:Vec n a) (ys:Vec m a) : Vec (n + m) a :=
    ( match xs in Vec n a return Vec m a -> Vec (n + m) a  with
      | Nil         => fun zs => zs
      | Cons x xs'  => fun zs => Cons x (append _ _ _ xs' zs)   
      end) ys.

Arguments append {a} {n} {m}.

Definition v3 : Vec 5 nat := append v1 v2.

Fixpoint append' (a:Type) (n m:nat) (xs:Vec' a n) (ys:Vec' a m) : Vec' a (n + m) :=
    match xs with
    | Nil'          => ys
    | Cons' x xs'   => Cons' x (append' _ _ _ xs' ys)
    end.

Arguments append' {a} {n} {m}.

Definition v3' : Vec' nat 5 := append' v1' v2'.

Fixpoint vec2vec' (a:Type) (n:nat) (xs:Vec n a) : Vec' a n :=
    match xs with
    | Nil           => Nil'
    | Cons x xs     => Cons' x (vec2vec' _ _ xs)
    end.

Fixpoint vec'2vec (a:Type) (n:nat) (xs:Vec' a n) : Vec n a :=
    match xs with
    | Nil'          => Nil
    | Cons' x xs    => Cons x (vec'2vec _ _ xs)
    end.

Arguments vec2vec' {a} {n}.
Arguments vec'2vec {a} {n}.

Definition vecId  (a:Type) (n:nat) (xs:Vec n a)  : Vec n a  := vec'2vec (vec2vec' xs).
Definition vecId' (a:Type) (n:nat) (xs:Vec' a n) : Vec' a n := vec2vec' (vec'2vec xs).

Arguments vecId  {a} {n}.
Arguments vecId' {a} {n}.

Compute vecId  v3.
Compute vecId' v3'.

Check Vec_ind.
Check Vec'_ind.

Fixpoint vecInd' (a:Type) 
    (P:forall (n:nat), Vec' a n -> Prop) 
    (H0:P 0 Nil')
    (IH:forall (n:nat) (x:a) (xs:Vec' a n), P n xs -> P (S n) (Cons' x xs))
    (n:nat) 
    (xs:Vec' a n)
    : P n xs :=
    match xs with 
    | Nil'       => H0
    | Cons' x ys => IH _ x ys (vecInd' a P H0 IH _ ys)
    end
    .

(*
Lemma vecIdent' : forall (a:Type) (n:nat) (xs:Vec' a n), vec2vec' (vec'2vec xs) = xs.
Proof.

Show.
*)

