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

End stream_eq_loop.


Require Import Arith.
Print fact.


CoFixpoint fact_slow' (n : nat) := Cons (fact n) (fact_slow' (S n)).
Definition fact_slow := fact_slow' 1.


CoFixpoint fact_iter' (cur acc : nat) := Cons acc (fact_iter' (S cur) (acc * cur)).
Definition fact_iter := fact_iter' 2 1.

Eval simpl in take 5 fact_slow.
Eval simpl in take 5 fact_iter.


Lemma fact_recur : forall n,
  fact n * S n = fact (S n).
  intro n.
  induction n.
  simpl.
  reflexivity.
  unfold fact.
  ring.
Qed.


Lemma fact_def : forall x n,
  fact_iter' x (fact n * S n) = fact_iter' x (fact (S n)).
  intros. 
  rewrite fact_recur.
  reflexivity.
Qed.

Hint Resolve fact_def.

Lemma fact_eq' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  intro n.
  apply(stream_eq_coind (fun s1 s2 => 
    exists n, s1 = fact_iter' (S n) (fact n) /\ s2 = fact_slow' n)); crush; eauto.
Qed.

Theorem fact_eq : stream_eq fact_iter fact_slow.
  apply fact_eq'.
Qed.

Section stream_eq_onequant.
  Variables A B : Type.
 
  Variables f g : A -> stream B.


  Hypothesis Cons_case_hd : forall x, head (f x) = head (g x).
  Hypothesis Cons_case_tl : forall x, exists y,tail (f x) = f y /\ tail (g x) = g y.
  
  Theorem stream_eq_onequant : forall x, stream_eq (f x) (g x).
    intro; apply (stream_eq_coind (fun s1 s2 => 
      exists x, s1 = f x /\ s2 = g x)); crush; eauto.
  Qed.
End stream_eq_onequant.


Lemma fact_eq'' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  apply stream_eq_onequant.
  simpl.
  reflexivity.
  simpl.
  eauto.
Qed.


Definition var := nat.

Definition vars := var -> nat.


Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if beq_nat v v' then n else vs v'.

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (e : exp) (env : vars) : nat :=
  match e with
    | Const n => n
    | Var v => env v
    | Plus e1 e2 => evalExp e1 env + evalExp e2 env
  end.

Inductive cmd : Set :=
| Assign : var -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd.




