Require Import bool.

Inductive list (a:Type) : Type :=
    | nil  : list a
    | cons : a -> list a -> list a
    .


Check nil.
Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).


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

Check repeat.
Check repeat'.
Check repeat''.
Check repeat'''.



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






