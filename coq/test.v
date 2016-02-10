Require Import List.

Require Import CpdtTactics.

Set Implicit Arguments.
(*Set Asymmetric Patterns.*)


Print unit.
Print True.

Section Propositional.
  Variables P Q R : Prop.

  Theorem obvious : True.
    apply I.
  Qed.

  Theorem obvious' : True.
    constructor.
  Qed.

  Print False.


  Theorem False_imp : False -> 2 + 2 = 5.
    destruct 1. (* case analysis *)
  Qed.

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
    intro.
    elimtype False.
    crush. (* how do we do it manually ? *)
  Qed.  


    Print not.

  Theorem arith_neq' : ~ (2 + 2 = 5).
    unfold not.
    crush.
  Qed.


  Print and.



  Theorem and_comm : P /\ Q -> Q /\ P.
    intro.
    destruct H.
    split.
    assumption.
    assumption.
  Qed.


  Print or.



  Theorem or_comm : P \/ Q -> Q \/ P.
    destruct 1.
    right.
    assumption.
    left.
    assumption.
  Qed.

  

  Theorem or_comm' : P \/ Q -> Q \/ P.
    tauto.
  Qed.

  
  Theorem arith_comm : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.

    intuition.
    rewrite app_length.
    tauto.
  Qed.

  Theorem arith_comm' : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    Hint Rewrite app_length.
    crush.
  Qed.

End Propositional. (* all our proved theorems become universally quantified
over the propositional variables that we used *)

Print ex.

  
Theorem exist1 : exists x : nat, x + 1 = 2.
  exists 1.
  simpl.
  reflexivity.
Qed.


Theorem exist2 : forall n m : nat, (exists x : nat, n + x = m) -> n <= m.
  intros.
  destruct H.
  crush.
Qed.



Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.


Theorem isZero_zero : isZero 0.
  constructor.
Qed.



Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
  destruct 1.
  crush.
Qed.

Theorem isZero_contra : isZero 1 -> False.
  destruct 1.
  Undo.
  inversion 1.
Qed.


Theorem isZero_contra' : isZero 1 -> 2 + 2 = 5.
  destruct 1.
  Abort.

Check isZero_ind.



Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).



Theorem even_0 : even 0.
  constructor.
Qed.


Theorem even_4 : even 4.
  constructor.
  constructor.
  constructor.
Qed.



Hint Constructors even.

  
Theorem even_4' : even 4.
  auto.
Qed.


Theorem even_1_contra : even 1 -> False.
  inversion 1.
Qed.



Theorem even_3_contra : even 3 -> False.
  inversion 1.
  inversion H1.
Qed.


Theorem even_plus : forall n m, even n -> even m -> even (n + m).
  induction n; crush.
  inversion H.
  simpl.
  constructor.
Restart.
  induction 1.
  simpl.
  intro.
  assumption.
  simpl.
  constructor.
  apply IHeven.
  assumption.
Qed.



Lemma even_succ : forall n, even n -> even (S n) -> False.
  induction 1.
  inversion 1.
  inversion 1.
  apply IHeven.
  assumption.
Qed.

Lemma even_n_plus_n : forall n, even(n + n).
  induction n.
  simpl.
  constructor.
  simpl.
  assert(n + (S n) = S(n + n)).
  crush.
  rewrite H.
  constructor.
  assumption.
Qed.

Theorem even_contra : forall n, even (S (n + n)) -> False.
  intro.
  assert(even(n + n)).
  apply even_n_plus_n.
  apply even_succ.
  assumption.
Qed.

SearchRewrite(_ + S _).







