Require Import List.

Require Import option.

Definition func1 (x y:option nat) : option nat :=
    match x with
    | None      => None
    | Some n    =>
        match y with
        | None      => None
        | Some m    => Some (n + m)
        end
    end.

Definition func2 (x y:option nat) : option nat :=
    x >>= (fun n  =>
    y >>= (fun m  =>
    ret (n + m))).


Definition func3 (x y:option nat) : option nat :=
    n <- x ;
    m <- y ;
    ret (n + m).

Definition func4 (x y:option nat) : option nat :=
    n <- x ;
    m <- y ;
    ret $ n + m.

Definition sample : list ((option nat) * ( option nat)) :=
    (cons (None,None) 
        (cons (Some 5, None)
            (cons (None,Some 5)
                (cons (Some 4,Some 5) nil)))).

Definition wrap (f:option nat -> option nat -> option nat) : list (option nat) := 
    map (fun x => 
            match x with
            | (u,v)     => f u v
            end) sample.

Definition test (f:option nat -> option nat -> option nat) : Prop := 
    wrap f = wrap func1.


Lemma test1 : test func1.
Proof. reflexivity. Qed.

Lemma test2 : test func2.
Proof. reflexivity. Qed.

Lemma test3 : test func3.
Proof. reflexivity. Qed.

Lemma test4 : test func4.
Proof. reflexivity. Qed.

Fixpoint even (n:nat) : bool :=
    match n with
    | 0     => true
    | S n   =>
        match n with
        | 0     => false
        | S n   => even n
        end
    end.

(* testing guards *)     
Definition func5 (x y:option nat) : option nat :=
    n <- x ;
    m <- y ;
    _ <- guard (even n);
    _ <- guard (even m);
    ret (n + m).

Lemma test5 : func5 None None = None.
Proof. reflexivity. Qed.

Lemma test6 : func5 None (Some 4) = None.
Proof. reflexivity. Qed.

Lemma test7 : func5 (Some 4) None = None.
Proof. reflexivity. Qed.

Lemma test8 : func5 (Some 3) (Some 5) = None.
Proof. reflexivity. Qed.

Lemma test9 : func5 (Some 4) (Some 5) = None.
Proof. reflexivity. Qed.

Lemma test10 : func5 (Some 3) (Some 6) = None.
Proof. reflexivity. Qed.

Lemma test11 : func5 (Some 4) (Some 6) = (Some 10). (* both even *)
Proof. reflexivity. Qed.
