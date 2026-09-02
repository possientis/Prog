Inductive eqPlus : forall (a:Type), a -> a -> Prop :=
| Base : forall (a:Type) (x:a), eqPlus a x x
| Func : forall (a b:Type) (f g:a -> b), 
    (forall (x:a), eqPlus b (f x) (g x)) -> eqPlus (a -> b) f g
.
