Inductive Vec : nat -> Type -> Type :=
| Nil   : forall (a:Type), Vec 0 a
| Cons  : forall (n:nat) (a:Type), a -> Vec n a -> Vec (S n) a
.

Check Vec.

Arguments Nil {a}.

Arguments Cons {n} {a}.


Definition cast1 (a:Type) (m:nat) (xs:Vec m a) : Vec (0 + m) a := xs.

Arguments cast1 {a} {m}.


Fixpoint append (a:Type) (n m:nat) (xs:Vec n a) (ys:Vec m a) : Vec (n + m) a :=
    match xs in Vec n' a' return Vec (n' + m) a' with
    | @Nil _        => cast1 ys
    | Cons x xs'    => Cons x (append _ _ _ xs' ys)
    end. 

