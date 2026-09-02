
Inductive unit : Set := 
| tt
.

Lemma unit_singleton : forall (x:unit), x = tt.
Proof. intros x. destruct x. reflexivity. Qed.


Inductive Empty_set : Set :=.

(*
Check Empty_set_ind.
*)

Lemma the_sky_is_falling : forall (x:Empty_set), 2 + 2 = 5.
Proof. intros x. destruct x. Qed.

Definition e2u (e:Empty_set) : unit := match e with end.

Inductive bool : Set := 
| true
| false
.

Definition negb(b:bool) : bool := if b then false else true.

Lemma negb_inverse : forall (b:bool), negb (negb b) = b.
Proof. intros b. destruct b; reflexivity. Qed.

Lemma negb_ineq : forall (b:bool), negb b <> b.
Proof. destruct b; discriminate. Qed.

(*
Check bool_ind.
*)

Inductive nat : Set :=
| O : nat
| S : nat -> nat
.

Definition isZero (n:nat) : bool :=
    match n with
    | O     => true
    | S _   => false
    end.

Definition pred (n:nat) : nat :=
    match n with 
    | O     => O
    | S m   => m
    end.


Fixpoint plus (n m:nat) : nat :=
    match n with 
    | O     => m
    | S p   => S (plus p m)
    end.

Lemma plus_O_n : forall (n:nat), plus O n = n.
Proof. intros n. reflexivity. Qed.

Lemma plus_n_O : forall (n:nat), plus n O = n.
Proof.
    intros n. induction n as [|n IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.

Lemma S_inj : forall (n m:nat), S n = S m -> n = m.
Proof. intros n m H. injection H. trivial. Qed.

Inductive list (a:Set) : Set :=
| Nil  : list a
| Cons : a -> list a -> list a
.

Arguments Nil {a}.
Arguments Cons {a} _ _.


Fixpoint length (a:Set) (xs:list a) : nat :=
    match xs with
    | Nil       => O
    | Cons x ys => S (length a ys)
    end.

Arguments length {a} _.

Lemma length_test : 
    length (Cons 0 (Cons 1 (Cons 2 Nil))) = S (S (S O)).
Proof. reflexivity. Qed.

Fixpoint append (a:Set) (xs ys:list a) : list a :=
    match xs with
    | Nil        => ys
    | Cons x xs' => Cons x (append a xs' ys)
    end.

Arguments append {a} _ _.


Lemma length_append : forall (a:Set) (xs ys:list a), 
    length (append xs ys) = plus (length xs) (length ys).
Proof.
    intros a xs. induction xs as [|x xs IH]; intros ys; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Qed.

Inductive btree (a:Set) : Set :=
| Leaf : btree a
| Node : btree a -> a -> btree a -> btree a
.

Arguments Leaf {a}.
Arguments Node {a} _ _ _.

Fixpoint size (a:Set) (t:btree a) : nat :=
    match t with
    | Leaf          => S O
    | Node t1 _ t2  => plus (size _ t1) (size _ t2)
    end.

Arguments size {a}.

Fixpoint splice (t1 t2:btree nat) : btree nat :=
    match t1 with
    | Leaf          => Node t2 O Leaf
    | Node s1 n s2  => Node (splice s1 t2) n s2
    end.

Lemma plus_assoc : forall (n m p:nat), plus (plus n m) p = plus n (plus m p).
Proof.
    intros n. induction n as [|n IH]; intros m p; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Qed.

Lemma plus_n_Sm : forall (n m:nat), plus n (S m) = S (plus n m).
Proof.
    intros n. induction n as [|n IH]; intros m; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Qed.

Lemma plus_comm : forall (n m:nat), plus n m = plus m n.
Proof.
    intros n. induction n as [|n IH]; intros m; simpl.
    - symmetry. apply plus_n_O.
    - rewrite IH. symmetry. apply plus_n_Sm.
Qed.

Lemma size_splice : forall (t1 t2:btree nat), 
    size (splice t1 t2) = plus (size t1) (size t2).
Proof.
    intros t1. induction t1 as [|s1 IH1 n s2 IH2]; intros t2; simpl.
    - rewrite plus_n_Sm. rewrite plus_n_O. reflexivity.  
    - rewrite IH1. rewrite plus_assoc.
      remember (plus (size t2) (size s2)) as e eqn:H.
      rewrite plus_comm in H. rewrite H. symmetry. apply plus_assoc.
Qed.


Inductive even_list (a:Set) : Set :=
| ENil  : even_list a
| ECons : a -> odd_list a -> even_list a
with odd_list (a:Set) : Set :=
| OCons : a -> even_list a -> odd_list a
.

Inductive list0 (a:Set) : Set :=
| Nil0  : list0 a
| Cons0 : a -> list2 a -> list0 a
with list1 (a:Set) : Set :=
| Cons1 : a -> list0 a -> list1 a
with list2 (a:Set) : Set :=
| Cons2 : a -> list1 a -> list2 a
.

Arguments Nil0 {a}.
Arguments Cons0 {a}.
Arguments Cons1 {a}.
Arguments Cons2 {a}.

Fixpoint length0 (a:Set) (xs: list0 a) : nat :=
    match xs with
    | Nil0       => O
    | Cons0 _ xs => S (length2 a xs)
    end
with length1 (a:Set) (xs:list1 a) : nat :=
    match xs with
    | Cons1 _ xs => S (length0 a xs)
    end
with length2 (a:Set) (xs:list2 a) : nat :=
    match xs with
    | Cons2 _ xs => S (length1 a xs)
    end
.

Arguments length0 {a}.
Arguments length1 {a}.
Arguments length2 {a}.




