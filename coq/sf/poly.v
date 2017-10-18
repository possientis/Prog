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
