Inductive tree (a:Type) : Type :=
| leaf : a -> tree a
| node : tree a -> tree a -> tree a
.

Arguments leaf {a} _.
Arguments node {a} _ _.

(*
Check tree_ind.
*)

(* This is not exactly what 'Check tree_ind' returns but equivalent to it *)
Definition tree_ind_principle : Prop := forall (a:Type), 
    forall (P:tree a -> Prop),
    (forall (x:a), P (leaf x))  ->
    (forall (t1 t2:tree a), P t1 -> P t2 -> P (node t1 t2)) ->
    forall (t:tree a), P t.

(* building some proof manually of equivalent statement *)
Fixpoint tree_ind_ (a:Type)(t:tree a) : forall (P:tree a -> Prop),
    (forall (x:a), P (leaf x))                                  ->
    (forall (t1 t2:tree a), P t1 -> P t2 -> P (node t1 t2))     -> P t :=
    fun (P:tree a -> Prop)                                                  =>
        fun (H0:forall (x:a), P (leaf x))                                   =>
            fun (H1:forall (t1 t2:tree a), P t1 -> P t2 -> P (node t1 t2))  =>
                match t with
                | leaf x        => H0 x
                | node t1 t2    => 
                    H1 t1 t2
                        (tree_ind_ a t1 P H0 H1)
                        (tree_ind_ a t2 P H0 H1)
                end.
(* so we now have a proof of our induction principle *)
Definition tree_ind' : tree_ind_principle := 
    fun a P H0 H1 t => tree_ind_ a t P H0 H1.


(* one constructor takes argument which is a function returning foo a b *)
Inductive foo (a b:Type) : Type :=
| bar  : a -> foo a b
| baz  : b -> foo a b
| quux : (nat -> foo a b) -> foo a b
.

(*
Check foo_ind.
*)









