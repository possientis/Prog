Require Import bool.
Require Import nat.
Require Import syntax.
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

Fixpoint ceval_fun_no_while (env:State) (c:com) : State :=
    match c with
    | SKIP                      => env
    | x ::= a1                  => t_update env x (aeval env a1)
    | c1 ;; c2                  => let env' := ceval_fun_no_while env c1 
                                   in ceval_fun_no_while env' c2
    | IFB b THEN c1 ELSE c2 FI  => if (beval env b)
                                   then ceval_fun_no_while env c1
                                   else ceval_fun_no_while env c2 
    | WHILE b DO c END          => env
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
.

Theorem ceval_deterministic: forall (c:com) (e e1 e2:State),
    ceval c e e1 -> ceval c e e2 -> e1 = e2.
Proof.
    intros c e e1 e2 H. revert e2. 
    induction H as 
        [e
        |e a n x Ha
        |e e' e'' c1 c2 H1 IH1 H2 IH2
        |e e' b c1 c2 Hb H1 IH1
        |e e' b c1 c2 Hb H1 IH1
        |e b c1 Hb
        |e e1 e2 b c1 Hb H1 IH1 H2 IH2
        ].
    - intros e' H. inversion H. reflexivity.
    - intros e' H. inversion H. subst. reflexivity.
    - intros e2 H. inversion H. subst.
        apply IH2. assert (e' = e'0) as H0.
            { apply IH1. assumption. }
        subst. assumption.
    - intros e1 H. inversion H.
        + subst. apply IH1. assumption.
        + assert (true = false) as E. 
            { rewrite <- Hb. assumption. }
            inversion E.
    - intros e1 H. inversion H.
        + assert (true = false) as E.
            { rewrite <- Hb. symmetry. assumption. }
            inversion E.
        + subst. apply IH1. assumption.
    - intros e' H. inversion H.
        + reflexivity.
        + assert (true = false) as E.
            { rewrite <- Hb. symmetry. assumption. } 
          inversion E.
    - intros e'' H. inversion H.
        + assert (true = false) as E.
            { rewrite <- Hb. subst. assumption. }
          inversion E.
        + subst. apply IH2. assert (e1 = e'). (* bad! we using e' *)
            { apply IH1. assumption. }
          subst. assumption.
Qed.

Theorem no_whiles_terminating : forall (c:com) (e:State),
    no_whilesR c -> exists (e':State), ceval c e e'. 
Proof.
    intros c e H. revert e. 
    induction H as [|k a|c1 c2 H1 IH1 H2 IH2|b c1 c2 H1 IH1 H2 IH2]. 
    - intros e. exists e. constructor.
    - intros e. exists (t_update e k (aeval e a)). constructor. reflexivity.
    - intros e. destruct (IH1 e) as [e1 E1]. destruct (IH2 e1) as [e2 E2].
        exists e2. apply E_Seq with (e':=e1).
        + assumption.
        + assumption.
    - intros e. destruct (beval e b) eqn:Eb.
        + destruct (IH1 e) as [e' H']. exists e'. apply E_IfTrue.
            { assumption. }
            { assumption. }
        + destruct (IH2 e) as [e' H']. exists e'. apply E_IfFalse.
            { assumption. }
            { assumption. }
Qed.
