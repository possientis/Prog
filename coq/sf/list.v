Require Import bool.
Require Import induction.

Inductive list (a:Type) : Type :=
    | nil  : list a
    | cons : a -> list a -> list a
    .


(*
Check nil.
Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).
*)


Fixpoint repeat {a:Type} (x:a) (count:nat) : list a :=
    match count with
    | 0     => nil a
    | S n   => cons a x (repeat x n)
    end.


Example repeat_test1 : repeat 3 0 = nil nat.
Proof. reflexivity. Qed.


Example repeat_test2 : repeat 3 1 = cons nat 3 (nil nat).
Proof. reflexivity. Qed.


Example repeat_test3 : repeat 3 2 = cons nat 3 (cons nat 3 (nil nat)).
Proof. reflexivity. Qed.

Module MUMBLEGRUMBLE.

Inductive mumble : Type :=
    | a : mumble
    | b : mumble -> nat -> mumble
    | c : mumble
    .

Inductive grumble (X:Type) : Type :=
    | d : mumble -> grumble X
    | e : X      -> grumble X
    .
(*
Check d mumble (b a 5). (* grumble mumble *)
Check d bool   (b a 5). (* grumble bool *)
Check e bool true.      (* grumble bool *)
Check e mumble (b c 0). (* grumble mumble *)
Check c.                (* mumble *)
*)

End MUMBLEGRUMBLE.

Fixpoint repeat' (a:Type) (x:a) (count:nat) : list a :=
    match count with
    | 0     => nil a
    | S n   => cons a x (repeat' a x n)
    end.


Fixpoint repeat'' a x count : list a :=
    match count with
    | 0     => nil a
    | S n   => cons a x (repeat'' a x n)
    end.

Fixpoint repeat''' a x count : list a :=
    match count with
    | 0     => nil _
    | S n   => cons _ x (repeat''' _ x n)
    end.

(*
Check repeat.
Check repeat'.
Check repeat''.
Check repeat'''.
*)


Definition list123  := cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {a}.
Definition list123'' := cons _ 1 (cons _ 2 (cons _ 3 nil)).

Arguments cons {a} _ _.
Definition list123''' := cons 1 (cons 2 (cons 3 nil)).


Example test_list123_1 : list123 = list123'.
Proof. reflexivity. Qed. 

Example test_list123_2 : list123 = list123''.
Proof. reflexivity. Qed. 

Example test_list123_3 : list123 = list123'''.
Proof. reflexivity. Qed. 

Notation "x :: xs" := (cons x xs) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..). (* syntax file has bug *)


Fixpoint app (a:Type) (k l: list a) : list a :=
    match k with
    | []        => l
    | x::xs     => x :: (app a xs l)
    end.  
     
Arguments app {a} _ _. (* type argument declared as implicit *)

Notation "l ++ k" := (app l k) (at level 60, right associativity). 


(* need a type annotation, as no other way for it to be inferred *)
Example test_app1 : forall a:Type, [] ++ [] = ([] : list a).
Proof. reflexivity. Qed.

Example test_app2 : forall (a:Type) (l:list a), [] ++ l = l.
Proof. reflexivity. Qed.

Example test_app3 : [1,2,3] ++ [4,5,6] = [1,2,3,4,5,6].
Proof. reflexivity. Qed.

Theorem  app_nil_r : forall (a:Type) (l:list a), l ++ [] = l.
Proof.
    induction l as [|x xs H].
    - reflexivity.
    - simpl. rewrite H. reflexivity.
Qed.

(* not computationally efficient *)
Fixpoint rev (a:Type) (l:list a) : list a :=
    match l with
    |   []          => []
    |   x :: xs     => (rev a xs) ++ [x]
    end.

Arguments rev {a} _.

Example test_rev1 : forall a:Type, rev [] = ([]:list a). 
Proof. reflexivity. Qed.

Example test_rev2 : rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.

Fixpoint length (a:Type) (l:list a) : nat :=
    match l with
    | []        => 0
    | (_::xs)   => S (length a xs)
    end.
        
Arguments length {a} _.

Example test_length1 : forall a:Type, length ([]:list a) = 0.
Proof. reflexivity. Qed.

Example test_length2 : length [1,2,3] = 3.
Proof. reflexivity. Qed.

Definition my_nil1 := ([]:list nat).
Definition my_nil2 : list nat := nil.
Definition my_nil3 := @nil.

Theorem app_assoc : forall (a:Type) (l m n: list a),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
    induction l as [|x xs H].
    - reflexivity.
    - simpl. intros m n. rewrite H. reflexivity.
Qed. 


Theorem app_length : forall (a:Type) (l k: list a),
    length (l ++ k) = length l + length k.
Proof.
    induction l as [| x xs H].
    - reflexivity.
    - intro k. simpl. rewrite H. reflexivity.
Qed.

Theorem rev_app_distr : forall (a:Type) (l k: list a),
    rev (l ++ k) = rev k ++ rev l.
Proof.
    induction l as [| x xs H].
    - intro k. simpl. rewrite app_nil_r. reflexivity.
    - intro k. simpl. rewrite H. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall (a:Type) (l: list a),
    rev (rev l) = l.
Proof.
    induction l as [|x xs H].
    - reflexivity.
    - simpl. rewrite rev_app_distr. simpl. rewrite H. reflexivity.
Qed.

(* we are not using app_length, exercise *)
Theorem app_length_cons : forall (a:Type) (l k:list a) (x:a) (n:nat),
    length (l ++ (x :: k)) = n -> S (length (l ++ k)) = n.
Proof.
    intros a l. induction l as [|y ys H].
    - intros k x n. simpl. intros H. exact H.
    - intros k x n. simpl. destruct n.
        + intros H'. inversion H'.
        + intros H'. inversion H' as [H1]. clear H'.
            rewrite H1. apply H in H1. rewrite H1. reflexivity.
Qed.

(* we are not using app_length, exercise *)
Theorem app_length_twice : forall (a:Type) (n:nat) (l:list a),
    length l = n -> length (l ++ l) = n + n.
Proof.
    intros a n l. generalize n. clear n. induction l as [|x xs H].
    - destruct n.
        + intros. reflexivity.
        + intros H. inversion H.
    - destruct n.
        + intros H'. inversion H'.
        + intros H'. inversion H' as [H1]. clear H'.
            simpl. rewrite H1. rewrite (plus_comm n (S n)).
            simpl. apply H in H1. 
            assert ( S (length (xs ++ xs)) = length (xs ++ x :: xs)) as H'.
                { apply app_length_cons with (x:=x). reflexivity. }
            rewrite <- H'. rewrite H1. reflexivity.
Qed.






