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







