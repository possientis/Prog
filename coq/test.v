Require Import List.

Require Import CpdtTactics.
(*
Definition bad : unit := tt.
*)

Set Implicit Arguments.
Set Asymmetric Patterns.



Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

CoFixpoint zeroes : stream nat := Cons 0 zeroes.


CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

Fixpoint take A (n : nat) (s : stream A) : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | Cons h t => h :: take n' t
      end
  end.

Eval simpl in take 10 zeroes.
Eval simpl in take 10 trues_falses.


Section map.
  Variables A B : Type.
  Variable f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with
      | Cons h t => Cons (f h) (map t)
    end.
End map.

Section interleave.
  Variable A : Type.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
      | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

(*
Section map'.
  Variables A B : Type.
  Variable f : A -> B.
  CoFixpoint map' (s : stream A) : stream B :=
    match s with
      | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t))
    end.
End map'.
*)

Definition tail A (s : stream A) : stream A :=
  match s with
    | Cons _ s' => s'
  end.


CoFixpoint ones : stream nat := Cons 1 ones.

Definition ones' := map S zeroes.

Theorem ones_eq : ones = ones'.
Abort.


Section stream_eq.
  Variable A : Type.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2, stream_eq t1 t2 -> stream_eq (Cons h t1)(Cons h t2).
End stream_eq.


Theorem ones_eq : stream_eq ones ones'.
  cofix.
  assumption.
  Undo.
  simpl.
Abort.

Definition frob A (s : stream A) : stream A :=
  match s with
    | Cons h t => Cons h t
  end.

Theorem frob_eq : forall A (s : stream A), s = frob s.
  destruct s.
  simpl.
  reflexivity.
Qed.

Theorem ones_eq : stream_eq ones ones'.
  cofix.
  rewrite (frob_eq ones).
  rewrite (frob_eq ones').
  simpl.
  constructor.
  fold (map S).
  fold ones'.
  assumption.
Qed.

Definition head A (s : stream A) : A :=
  match s with
    | Cons x _ => x
  end.


Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.


  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> head s1 = head s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tail s1) (tail s2).

  
  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
    cofix.
    destruct s1.
    destruct s2.
    intro.
    generalize (Cons_case_hd H).
    intro Heq.
    simpl in Heq.
    rewrite Heq.
    constructor.
    apply stream_eq_coind.
    apply (Cons_case_tl H).
  Qed.
End stream_eq_coind.

Print stream_eq_coind. 


Theorem ones_eq'' : stream_eq ones ones'.
  apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')); crush.
Qed.



Section stream_eq_loop.
  Variable A : Type.
  Variables s1 s2 : stream A.

  Hypothesis Cons_case_hd : head s1 = head s2.
  Hypothesis loop1 : tail s1 = s1.
  Hypothesis loop2 : tail s2 = s2.
  
  Theorem stream_eq_loop : stream_eq s1 s2.
    apply (stream_eq_coind (fun s1' s2' => s1' = s1 /\ s2' = s2)); crush.
  Qed.






