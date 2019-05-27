Definition ret (a:Type) (x:a) : option a := Some x.

Arguments ret {a} _.

Definition bind (a b:Type) (k:option a) (f:a -> option b) : option b :=
    match k with
    | None      => None
    | Some x    =>
        match (f x) with
        | None      => None
        | Some y    => Some y
        end
    end.

Arguments bind {a} {b} _ _.

Notation "k >>= f" := (bind k f) (at level 50, left associativity).

Notation "x <- k ; k'" := (k >>= (fun x => k')) 
    (at level 60, right associativity).


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

Definition ap (a b:Type) (f:a -> b) (x:a) : b := f x.
Arguments ap {a} {b} _ _.

Notation "f $ x" := (ap f x) (at level 60).

Definition func4 (x y:option nat) : option nat :=
    n <- x ;
    m <- y ;
    ret $ n + m.

Definition test (f:option nat -> option nat -> option nat) (x y:option nat) 
    : Prop := f x y = func1 x y.

Example func2_test1 : test func2 None None.
Proof. reflexivity. Qed.

Example func2_test2 : test func2 (Some 5) None.
Proof. reflexivity. Qed.

Example func2_test3 : test func2 None (Some 5).
Proof. reflexivity. Qed.
    
Example func2_test4 : test func2 (Some 4) (Some 5).
Proof. reflexivity. Qed.

Example func3_test1 : test func3 None None.
Proof. reflexivity. Qed.

Example func3_test2 : test func3 (Some 5) None.
Proof. reflexivity. Qed.

Example func3_test3 : test func3 None (Some 5).
Proof. reflexivity. Qed.

Example func3_test4 : test func3 (Some 4) (Some 5).
Proof. reflexivity. Qed.

Example func4_test1 : test func4 None None.
Proof. reflexivity. Qed.

Example func4_test2 : test func4 (Some 5) None.
Proof. reflexivity. Qed.

Example func4_test3 : test func4 None (Some 5).
Proof. reflexivity. Qed.

Example func4_test4 : test func4 (Some 4) (Some 5).
Proof. reflexivity. Qed.

(* TODO: define guard : bool -> option unit *)
Definition a : unit := tt.
