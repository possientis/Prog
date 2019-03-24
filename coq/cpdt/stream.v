Require Import List.

CoInductive Stream (a:Type) : Type :=
| Cons : a -> Stream a -> Stream a
.

Arguments Cons {a} _ _.


CoFixpoint zeroes : Stream nat := Cons 0 zeroes.

CoFixpoint from (n:nat) : Stream nat := Cons n (from (S n)).

Definition nats : Stream nat := from 0.

CoFixpoint trues_falses : Stream bool := Cons true falses_trues
with falses_trues : Stream bool := Cons false trues_falses.

CoFixpoint trues_falses' : Stream bool := Cons true (Cons false trues_falses').


Fixpoint take (a:Type) (n:nat) (s:Stream a) : list a :=
    match n with
    | 0     => nil
    | S p   => 
        match s with
        | Cons h t      => h :: take a p t
        end
    end.

Arguments take {a} _ _.

Example take_test1 : take 5 zeroes = 0::0::0::0::0::nil.
Proof. reflexivity. Qed.


Example take_test2 : take 6 nats = 0::1::2::3::4::5::nil.
Proof. reflexivity. Qed.


Example take_test3 : take 3 trues_falses = true::false::true::nil.
Proof. reflexivity. Qed.

CoFixpoint map' (a b:Type) (f:a -> b) (s:Stream a) : Stream b :=
    match s with
    | Cons h t  => Cons (f h) (map' a b f t)
    end.

Arguments map' {a} {b} _ _.

Definition map (a b:Type) (f:a -> b) : Stream a -> Stream b :=
    cofix g (s:Stream a) : Stream b :=
        match s with
        | Cons h t  => Cons(f h) (g t)
        end.

Arguments map {a} {b} _ _.

(*
Lemma map_same : forall (a b:Type) (f:a -> b) (s:Stream a), map f s = map' f s.
Proof.
    intros a b f [h t]. simpl.

Show.
*)

