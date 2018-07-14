Require Import bool.
Require Import nat.
Require Import hsyntax.
Require Import state.
Require Import dictionary.


Fixpoint aeval (env:State) (a:aexp) : nat :=
    match a with
    | ANum n        => n
    | AKey k        => env k
    | APlus a1 a2   => (aeval env a1) + (aeval env a2)
    | AMinus a1 a2  => (aeval env a1) - (aeval env a2)
    | AMult a1 a2   => (aeval env a1) * (aeval env a2) 
    end.


Fixpoint beval (env:State) (b:bexp) : bool :=
    match b with
    | BTrue         => true
    | BFalse        => false
    | BEq a1 a2     => eqb (aeval env a1) (aeval env a2)
    | BLe a1 a2     => leb (aeval env a1) (aeval env a2)
    | BNot b1       => negb (beval env b1)
    | BAnd b1 b2    => andb (beval env b1) (beval env b2)
    end.

Inductive ceval : com -> State -> State -> Prop :=
| E_Skip     : forall e, ceval SKIP e e
| E_Ass      : forall e a n x, aeval e a = n -> ceval (x ::= a) e (t_update e x n)
| E_Seq      : forall e e' e'' c1 c2, ceval c1 e e' -> ceval c2 e' e'' ->
                ceval (c1 ;; c2) e e''
| E_IfTrue   : forall e e' b c1 c2, beval e b = true -> ceval c1 e e' ->
                ceval (IFB b THEN c1 ELSE c2 FI) e e'
| E_IfFalse  : forall e e' b c1 c2, beval e b = false -> ceval c2 e e' ->
                ceval (IFB b THEN c1 ELSE c2 FI) e e'
| E_WhileEnd : forall e b c, beval e b = false -> ceval (WHILE b DO c END) e e
| E_WhileLoop: forall e e' e'' b c, beval e b = true -> ceval c e e' ->
                ceval (WHILE b DO c END) e' e'' -> 
                ceval (WHILE b DO c END) e  e''
| E_Havoc    : forall e k n, ceval (CHavoc k) e (t_update e k n)
.

Example havoc_test1 : ceval (HAVOC x) emptyState (t_update emptyState x 0).
Proof. constructor. Qed.

Example havoc_test2 : ceval (SKIP ;; HAVOC z) emptyState (t_update emptyState z 20).
Proof. apply E_Seq with emptyState; constructor. Qed.


Lemma ceval_havoc: forall (k:Key) (e e':State),
    ceval (HAVOC k) e e' -> exists n, e' = t_update e k n. 
Proof.
    intros k e e' H. remember (HAVOC k) as c eqn:C. revert C.
    destruct H; intros H'; inversion H'; subst.
    exists n. reflexivity.
Qed.


