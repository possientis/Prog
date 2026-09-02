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

Arguments bar {a} {b} _.
Arguments baz {a} {b} _.
Arguments quux {a} {b} _.

(*
Check foo_ind.
*)

Definition foo_ind_principle : Prop := forall (a b:Type),
    forall (P:foo a b -> Prop),
    (forall (x:a), P (bar x))                                       ->
    (forall (y:b), P (baz y))                                       ->
    (forall (f:nat -> foo a b), (forall n, P (f n)) -> P (quux f))  ->
    forall (z:foo a b), P z.


(* we could drop some requirement, but less likely to be useful *)
(* same conclusion, but with stronger hypothesis                *)
Definition foo_ind_principle_weak : Prop := forall (a b:Type),
    forall (P:foo a b -> Prop),
    (forall (x:a), P (bar x))                                       ->
    (forall (y:b), P (baz y))                                       ->
    (forall (f:nat -> foo a b), P (quux f)) (* harder to prove *)   ->
    forall (z:foo a b), P z.

Lemma weak_is_weaker : foo_ind_principle -> foo_ind_principle_weak.
Proof.
    unfold foo_ind_principle_weak. intros H a b P H0 H1 H2 z. apply H.
    - exact H0.
    - exact H1.
    - intros f H'. apply H2.
Qed.



(* building some proof manually of equivalent statement *)
(* Why does this terminate ? *)
Fixpoint foo_ind_ (a b:Type) (z:foo a b) : forall (P:foo a b -> Prop),
    (forall (x:a), P (bar x))                                       ->
    (forall (y:b), P (baz y))                                       ->
    (forall (f:nat -> foo a b), (forall n, P (f n)) -> P (quux f))  -> P z :=
    fun (P:foo a b -> Prop)                                         =>
        fun (H0:forall (x:a), P (bar x))                            =>
            fun (H1:forall (y:b), P (baz y))                        =>
                fun (H2: forall (f:nat -> foo a b),
                        (forall n, P (f n)) -> P (quux f))          =>
                            match z with
                            | bar x     => H0 x
                            | baz y     => H1 y
                            | quux f    => H2 f 
                                (fun n => foo_ind_ a b (f n) P H0 H1 H2)   
                            end.

Definition foo_ind' (a b:Type) : forall (P:foo a b -> Prop),
    (forall (x:a), P (bar x))                                       ->
    (forall (y:b), P (baz y))                                       ->
    (forall (f:nat -> foo a b), (forall n, P (f n)) -> P (quux f))  ->
    forall (z:foo a b), P z :=
    fun P H0 H1 H2 z => foo_ind_ a b z P H0 H1 H2.









