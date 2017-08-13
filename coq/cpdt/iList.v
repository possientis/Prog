Set Implicit Arguments.
Require Import List.


Section iList.

Variable A:Set.
Variable x y z: A.

Inductive iList : nat -> Set :=
    | Nil   : iList 0
    | Cons  : forall n, A -> iList n -> iList (S n)
    .

(* Definingth length function becomes very simple *)
Definition iLength {n:nat}(l: iList n) : nat := n.

Definition L0 := Nil.
Definition L1 := Cons x L0.
Definition L2 := Cons y L1.
Definition L3 := Cons z L2.
 
Compute iLength L0.
Compute iLength L1.
Compute iLength L2.
Compute iLength L3.


Fixpoint app {n1 n2:nat}(l1:iList n1)(l2:iList n2) : iList (n1+n2) :=
    match l1 with
        | Nil           =>  l2
        | Cons a l1'    =>  Cons a (app l1' l2)
    end.

Compute app L0 L0.
Compute app L0 L1.
Compute app L1 L0.
Compute app L0 L2.
Compute app L2 L0.
Compute app L1 L2.
Compute app L2 L1.


Fixpoint app' {n1 n2:nat}(l1:iList n1)(l2:iList n2) : iList (n1 + n2) :=
    match l1 in (iList n1) return (iList (n1 + n2)) with
        | Nil           => l2
        | Cons a l1'    => Cons a (app' l1' l2)
    end.

Compute app' L1 L2.

Fixpoint inject (ls : list A) : iList (length ls) :=
    match ls with
        | nil           => Nil
        | h :: ts       => Cons h (inject ts)
    end.

Definition l0 : list A := nil.
Definition l1 := x::l0.
Definition l2 := y::l1.
Definition l3 := z::l2.

Fixpoint unject {n:nat}(ls:iList n) : list A :=
    match ls with
        | Nil           => nil
        | Cons a ls'     => a :: unject ls'
    end.

Compute unject L3.

Theorem inject_inverse : forall ls, unject (inject ls) = ls.
Proof.
    intro ls. elim ls.
    clear ls. simpl. reflexivity.
    clear ls. intros a l H. simpl. rewrite H. reflexivity.
Qed.

(*        | Nil           => ???  *)
Definition iHead {n:nat} (ls:iList (S n)) : A :=
    match ls with 
        | Cons a _      => a
    end.

Compute iHead L3.
Compute iHead L2.
Compute iHead L1.

Definition iHead' {n:nat} (ls:iList (S n)) : A :=
    match ls in (iList (S n)) with
        | Cons a _      => a
    end.

Compute iHead' L3.
Compute iHead' L2.
Compute iHead' L1.


Definition iHead0 {n:nat}(ls:iList n) :=
match ls in (iList n) return (match n with 0 => unit | S _ => A end) with
    | Nil               => tt
    | Cons a _          => a
end.

Check iHead0.


Definition iHead'' {n:nat}(ls:iList (S n)) : A := iHead0 ls.


Compute iHead'' L3.
Compute iHead'' L2.
Compute iHead'' L1.

End iList.


