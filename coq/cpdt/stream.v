Require Import List.

CoInductive Stream (a:Type) : Type :=
| Cons : a -> Stream a -> Stream a
.

Arguments Cons {a} _ _.

Definition head (a:Type) (s:Stream a) : a :=
    match s with
    | Cons x _  => x
    end.

Arguments head {a} _.


Definition tail (a:Type) (s:Stream a) : Stream a :=
    match s with
    | Cons _ t  => t
    end.

Arguments tail {a} _.

Fixpoint take (a:Type) (n:nat) (s:Stream a) : list a :=
    match n with
    | 0     => nil
    | S p   => 
        match s with
        | Cons h t      => h :: take a p t
        end
    end.

Arguments take {a} _ _.

(* our experience of induction suggests this may not be the best *)
CoFixpoint map' (a b:Type) (f:a -> b) (s:Stream a) : Stream b :=
    match s with
    | Cons h t  => Cons (f h) (map' a b f t)
    end.

Arguments map' {a} {b} _ _.

(* our experience of induction suggests this could be better *)
Definition map (a b:Type) (f:a -> b) : Stream a -> Stream b :=
    cofix g (s:Stream a) : Stream b :=
        match s with
        | Cons h t  => Cons(f h) (g t)
        end.

Arguments map {a} {b} _ _.

CoFixpoint zeroes : Stream nat := Cons 0 zeroes.

CoFixpoint from (n:nat) : Stream nat := Cons n (from (S n)).

Definition nats : Stream nat := from 0.

CoFixpoint ones : Stream nat := Cons 1 ones.
Definition ones': Stream nat := map S zeroes.

Example take_test1 : take 5 zeroes = 0::0::0::0::0::nil.
Proof. reflexivity. Qed.


Example take_test2 : take 6 nats = 0::1::2::3::4::5::nil.
Proof. reflexivity. Qed.




CoFixpoint interleave (a:Type) (s1 s2:Stream a) : Stream a :=
    match s1, s2 with
    | Cons h1 t1, Cons h2 t2    => Cons h1 (Cons h2 (interleave a t1 t2))
    end.

Arguments interleave {a} _ _.

(* unguarded recursive call 
CoFixpoint bizarre (a b:Type) (f:a -> b) (s:Stream a) : Stream b :=
    match s with
    | Cons h t => interleave (Cons (f h) (bizarre a b f t)) (Cons (f h) (bizarre a b f t))
    end.
*)

(* unguarded recursive call 
CoFixpoint bad : Stream nat := tail (Cons 0 bad).
*)



CoInductive stream_eq (a:Type) : Stream a -> Stream a -> Prop :=
| Stream_eq : forall (x:a) (t1 t2:Stream a), 
    stream_eq a t1 t2 -> stream_eq a (Cons x t1) (Cons x t2).

Arguments stream_eq  {a} _ _.

Lemma stream_eq_coind : forall (a:Type) (R:Stream a -> Stream a -> Prop),
    (forall (s1 s2:Stream a), R s1 s2 -> head s1 = head s2)     ->
    (forall (s1 s2:Stream a), R s1 s2 -> R (tail s1) (tail s2)) ->
    (forall (s1 s2:Stream a), R s1 s2 -> stream_eq s1 s2).
Proof.
    intros a R Hhead Htail. cofix. intros [h1 t1] [h2 t2] H.
    generalize H. intro H'. 
    apply Hhead in H'. simpl in H'. 
    rewrite H'. constructor. 
    apply stream_eq_coind. 
    apply Htail in H. simpl in H. 
    assumption.
Qed.

(* direct proof *)
Lemma stream_eq_refl : forall (a:Type) (s:Stream a), stream_eq s s.
Proof.
    intros a. cofix. intros [h t]. 
    constructor. apply stream_eq_refl.
Qed.

(* proof using coinduction principle *)
Lemma stream_eq_refl' : forall (a:Type) (s:Stream a), stream_eq s s.
Proof.
    intros a s. apply (stream_eq_coind a (fun x y => x = y)).
    - clear s. intros s1 s2 H. rewrite H. reflexivity.
    - clear s. intros s1 s2 H. rewrite H. reflexivity.
    - reflexivity.
Qed.

(* proof using coinduction principle *)
Lemma stream_eq_sym : forall (a:Type) (s1 s2:Stream a), 
    stream_eq s1 s2 -> stream_eq s2 s1.
Proof.
    intros a s1 s2 H. apply (stream_eq_coind a (fun x y => stream_eq y x)).
    - clear s1 s2 H. intros s1 s2 H. destruct H. reflexivity.
    - clear s1 s2 H. intros s1 s2 H. destruct H. assumption.
    - assumption.
Qed.


(*
(* not quite the same as 'id' *)
Definition frob (a:Type) (s:Stream a) : Stream a :=
    match s with
    | Cons h t  => Cons h t
    end.

Arguments frob {a} _.

(* seems pointless and yet ... *)
Lemma frob_same : forall (a:Type) (s:Stream a), s = frob s.
Proof. intros a [h t]. reflexivity. Qed.

Arguments frob_same {a} _.

Lemma ones_same : stream_eq ones ones'.
Proof. 
    cofix. 
    rewrite (frob_same ones).
    rewrite (frob_same ones').
    simpl. constructor. assumption.
Qed.


Lemma map_same : forall (a b:Type) (f:a -> b) (s:Stream a), stream_eq (map f s) (map' f s).
Proof.
    intros a b f. cofix. intros [h t].
    rewrite (frob_same (map  f (Cons h t))).
    rewrite (frob_same (map' f (Cons h t))).
    simpl. constructor. apply map_same.
Qed.



(* we apply this coinduction principle *)

Lemma ones_same' : stream_eq ones ones'.
Proof.



Show.

*)
