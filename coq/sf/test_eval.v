Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import Imp_code.

Example test_aeval0 : forall (env:State), aeval env (ANum 17) = 17.
Proof. reflexivity. Qed.


Example test_aeval1 : forall (env:State), aeval env (APlus (ANum 2) (ANum 5)) = 7.
Proof. reflexivity. Qed.


Example test_aeval2 : forall (env:State), aeval env (AMinus (ANum 12) (ANum 5)) = 7.
Proof. reflexivity. Qed.


Example test_aeval3 : forall (env:State), aeval env (AMult (ANum 4) (ANum 5)) = 20.
Proof. reflexivity. Qed.

Example test_ceval1 : ceval (
    x ::= ANum 2;;
    IFB BLe (AKey x) (ANum 1)
        THEN y ::= ANum 3
        ELSE z ::= ANum 4
    FI) 
    emptyState
    (t_update (t_update emptyState x 2) z 4).
Proof.
    apply E_Seq with (e' := t_update emptyState x 2).
    - apply E_Ass. reflexivity.
    - apply E_IfFalse.
        + reflexivity.
        + apply E_Ass. reflexivity.
Qed.

Theorem test_ceval2 : ceval pup_to_n 
    (t_update emptyState x 3)
    (t_update
        (t_update
            (t_update 
                (t_update
                    (t_update 
                        (t_update 
                            (t_update 
                                (t_update 
                                    emptyState 
                                    x 3)  y 0) y 3) x 2) y 5) x 1) y 6) x 0).
Proof.
    remember (t_update emptyState x 3) as e0 eqn:E0.
    remember (t_update e0 y 0) as e1 eqn:E1.
    remember (t_update e1 y 3) as e2 eqn:E2.
    remember (t_update e2 x 2) as e3 eqn:E3.
    remember (t_update e3 y 5) as e4 eqn:E4.
    remember (t_update e4 x 1) as e5 eqn:E5.
    remember (t_update e5 y 6) as e6 eqn:E6.
    remember (t_update e6 x 0) as e7 eqn:E7. 
    apply E_Seq with (e':=e1).
        - rewrite E1. apply E_Ass. reflexivity.
        - apply E_WhileLoop with (e':=e3).
            + rewrite E1, E0. reflexivity.  
            + apply E_Seq with (e':=e2). 
                { rewrite E2. apply E_Ass. 
                    rewrite E1, E0. reflexivity. }
                { rewrite E3. apply E_Ass. 
                    rewrite E2, E1, E0. reflexivity. }  
            + apply E_WhileLoop with (e':=e5).
                { rewrite E3, E2, E1, E0. reflexivity. }
                { rewrite E5. apply E_Seq with (e':=e4).
                    { rewrite E4. apply E_Ass. 
                        rewrite E3, E2, E1, E0. reflexivity. }
                    { apply E_Ass. 
                        rewrite E4, E3, E2, E1, E0. reflexivity. } }
                { apply E_WhileLoop with (e':=e7).
                    { rewrite E5, E4, E3, E2, E1, E0. reflexivity. }
                    { apply E_Seq with (e':=e6).
                        { rewrite E6. apply E_Ass. 
                            rewrite E5, E4, E3, E2, E1, E0. reflexivity. }
                        { rewrite E7. apply E_Ass.
                            rewrite E6, E5, E4, E3, E2, E1, E0. reflexivity. } }
                    { apply E_WhileEnd.
                        rewrite E7, E6, E5, E4, E3, E2, E1, E0. reflexivity. }}
Qed. 


Theorem test_ceval3 : forall (e e':State) (n:nat),
    e x = n -> ceval Add2_x e e' -> e' x = n + 2.
Proof.
    intros e e' n H0 H1. unfold Add2_x in H1. inversion H1. subst. simpl.
    unfold t_update. reflexivity.
Qed.


Theorem test_ceval4 : forall (e e':State) (n m:nat),
    e x = n -> e y = m -> ceval Mult_x_y_z e e' -> e' z = n*m.
Proof.
    intros e e' n m Hx Hy H. unfold Mult_x_y_z in H. inversion H. subst.
    simpl. unfold t_update. reflexivity.
Qed.

(* infinite loop never stop *)
Theorem test_ceval5 : forall (e e':State), ~ceval loop e e'.
Proof.
    intros e e' H. unfold loop in H.
    remember (WHILE BTrue DO SKIP END) as c eqn:Hc. revert Hc. 
    induction H as
        [e
        |e a n x H0
        |e e' e'' c1 c2 H1 IH1 H2 IH2
        |e e' b c1 c2 H0 H1 IH1
        |e e' b c1 c2 H0 H1 IH1
        |e b c H0
        |e e' e'' b c H0 H1 IH1 H2 IH2
        ].
    - intros H'. inversion H'.
    - intros H'. inversion H'.
    - intros H'. inversion H'.
    - intros H'. inversion H'.
    - intros H'. inversion H'.
    - intros H'. inversion H'. subst. assert (true = false) as E.
        { assumption. } inversion E.
    - intros H'. apply IH2. exact H'.
Qed.





