Inductive Vec : nat -> Type -> Type :=
| Nil   : forall (a:Type), Vec 0 a
| Cons  : forall (n:nat) (a:Type), a -> Vec n a -> Vec (S n) a
.


Inductive Vec' (a:Type) : nat -> Type :=
| Nil'   : Vec' a 0
| Cons'  : forall (n:nat), a -> Vec' a n -> Vec' a (S n)
.

Check Vec.
Check Vec'.

Check Nil.
Check Nil'.

Check Cons.
Check Cons'.

Fixpoint append' (a:Type) (n m:nat) (xs:Vec' a n) (ys:Vec' a m) : Vec' a (n + m) :=
    match xs with
    | Nil' _            => ys
    | Cons' _ _ x xs'   => Cons' _ _ x (append' _ _ _ xs' ys)
    end.

Fail Fixpoint append (a:Type) (n m:nat) (xs:Vec n a) (ys:Vec m a) : Vec (n + m) a :=
    match xs with
    | Nil _             => ys
    | Cons _ _ x xs'    => Cons _ _ x (append _ _ _ xs' ys)   
    end.

Print Vec.
Print Vec'.

Fixpoint vec2vec' (a:Type) (n:nat) (xs:Vec n a) : Vec' a n :=
    match xs with
    | Nil _             => Nil' _
    | Cons _ _ x xs     => Cons' _ _ x (vec2vec' _ _ xs)
    end.

Fixpoint vec'2vec (a:Type) (n:nat) (xs:Vec' a n) : Vec n a :=
    match xs with
    | Nil' _            => Nil _
    | Cons' _ _ x xs    => Cons _ _ x (vec'2vec _ _ xs)
    end.

Arguments vec2vec' {a} {n}.
Arguments vec'2vec {a} {n}.

Lemma vecId : forall (a:Type) (n:nat) (xs:Vec n a), vec'2vec (vec2vec' xs) = xs.
Proof.
    intros a n. revert n a. induction n as [|n IH].
    - admit.
    - intros a xs. destruct xs as [|m b x xs].
        + admit.
        + simpl.

Show.


(*
Definition cast1 (a:Type) (m:nat) (xs:Vec m a) : Vec (0 + m) a := xs.

Arguments cast1 {a} {m}.


Fixpoint append (a:Type) (n m:nat) (xs:Vec n a) (ys:Vec m a) : Vec (n + m) a :=
    match xs in Vec n' a' return Vec (n' + m) a' with
    | @Nil _        => cast1 ys
    | Cons x xs'    => Cons x (append _ _ _ xs' ys)
    end. 
*)
