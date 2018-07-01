Require Import bool.
Require Import nat. 
Require Import syntax.
Require Import eval.
Require Import dictionary.
Require Import state.


Definition aequiv (a1 a2:aexp) : Prop :=
  forall (e:State), aeval e a1 = aeval e a2.

Definition bequiv (b1 b2:bexp) : Prop :=
  forall (e:State), beval e b1 = beval e b2.

Definition cequiv (c1 c2:com)  : Prop :=
  forall (e e':State), ceval c1 e e' <-> ceval c2 e e'. 


Theorem skip_left : forall (c:com), cequiv (SKIP ;; c) c.
Proof.
    intros c e e'. split.
    - intros H. inversion H. subst. inversion H2. subst. assumption.
    - intros H. simpl. apply E_Seq with e.
        + constructor.
        + assumption.
Qed.

Theorem skip_right : forall (c:com), cequiv (c ;; SKIP) c.
Proof.
    intros c e e'. split.
    - intros H. inversion H. subst. inversion H5. subst. assumption.
    - intros H. simpl. apply E_Seq with e'.
        + assumption.
        + constructor.
Qed.

Theorem if_true_simple : forall (c1 c2:com), 
    cequiv (IFB BTrue THEN c1 ELSE c2 FI) c1.
Proof.
    intros c1 c2 e e'. split.
    - intros H. inversion H; subst.
        + assumption.
        + inversion H5.
    - intros H. apply E_IfTrue.
        + reflexivity.
        + assumption.
Qed.
    
Theorem if_true : forall (b:bexp) (c1 c2:com),
    bequiv b BTrue -> cequiv (IFB b THEN c1 ELSE c2 FI) c1.
Proof.
    intros b c1 c2 H e e'. unfold bequiv in H. simpl in H. split.
    - intros H'. inversion H'; subst.
        + assumption.
        + rewrite (H e) in H5. inversion H5. 
    - intros H'. apply E_IfTrue.
        + apply H.
        + assumption.
Qed.

Theorem if_false : forall (b:bexp) (c1 c2:com),
    bequiv b BFalse -> cequiv (IFB b THEN c1 ELSE c2 FI) c2.
Proof.
    intros b c1 c2 H e e'. unfold bequiv in H. simpl in H. split.
    - intros H'. inversion H'; subst.
        + rewrite (H e) in H5. inversion H5. 
        + assumption.
    - intros H'. apply E_IfFalse.
        + apply H.
        + assumption.
Qed.

Theorem swap_if_branches : forall (b:bexp) (c1 c2:com),
    cequiv (IFB b THEN c1 ELSE c2 FI) (IFB (BNot b) THEN c2 ELSE c1 FI).
Proof.
    intros b c1 c2 e e'. split.
    - intros H. inversion H; subst.
        + apply E_IfFalse.
            { simpl. rewrite H5. reflexivity. }
            { assumption. }
        + apply E_IfTrue.
            { simpl.  rewrite H5. reflexivity. }
            { assumption. }
    - intros H. inversion H; subst.
        + apply E_IfFalse.
            { simpl in H5. destruct (beval e b).
                { inversion H5. }
                { reflexivity. } }
            { assumption. }
        + apply E_IfTrue.
            { simpl in H5. destruct (beval e b).
                { reflexivity. }
                { inversion H5. } }
            { assumption. }
Qed.


Theorem while_false : forall (b:bexp) (c:com),
    bequiv b BFalse -> cequiv (WHILE b DO c END) SKIP.
Proof.
    intros b c H e e'. unfold bequiv in H. simpl in H. split.
    - intros H'. inversion H'; subst.
        + constructor.
        + rewrite (H e) in H2. inversion H2.
    - intros H'. inversion H'. subst. constructor. apply H.
Qed.

Lemma while_true_nonterm : forall (b:bexp) (c:com) (e e':State),
    bequiv b BTrue -> ~(ceval (WHILE b DO c END) e e').
Proof.
    intros b c e e' H H'. remember (WHILE b DO c END) as c' eqn:H0.
    revert H0. induction H'.
    - intros H1. inversion H1.
    - intros H1. inversion H1.
    - intros H1. inversion H1.
    - intros H1. inversion H1.
    - intros H1. inversion H1.
    - intros H1. inversion H1. subst. unfold bequiv in H. simpl in H.
        rewrite (H e) in H0. inversion H0.
    - assumption.
Qed.


Theorem while_true : forall (b:bexp) (c:com),
    bequiv b BTrue -> cequiv (WHILE b DO c END) (WHILE BTrue DO SKIP END).
Proof.
    intros b c H e e'. split.
    - intros H'. exfalso. apply while_true_nonterm with (b)(c)(e)(e').
        + assumption.
        + assumption.
    - intros H'. exfalso. apply while_true_nonterm with (BTrue)(SKIP)(e)(e').
        + unfold bequiv. reflexivity.
        + assumption.
Qed.

Theorem seq_assoc : forall (c1 c2 c3:com),
    cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
    intros c1 c2 c3 e e'. split.
    - intros H. inversion H. subst. inversion H2. subst.
        apply E_Seq with e'1.
            + assumption.
            + apply E_Seq with e'0.
                { assumption. }
                { assumption. }
    - intros H. inversion H. subst. inversion H5. subst. apply E_Seq with e'1.
        + apply E_Seq with e'0.
            { assumption. }
            { assumption. }
        + assumption.
Qed.


Theorem identity_assignement : forall (k:Key),
    cequiv (k ::= AKey k) SKIP.
Proof.
    intros k e e'. split.
    - intros H. inversion H; subst. simpl. simpl in H.
        remember (t_update e k (e k)) as e' eqn:E.
        assert (e' = e) as H'.
            { rewrite E. apply t_update_same. }
        rewrite H'. constructor.
    - intros H. inversion H; subst. remember e' as e eqn:E. 
        rewrite E at 2.
        rewrite <- t_update_same with (_)(e')(k).
        rewrite <- E. constructor. reflexivity.
Qed.

Theorem aequiv_assignment : forall (k:Key) (a:aexp),
    aequiv (AKey k) a -> cequiv SKIP (k ::= a).
Proof.
    intros k a H e e'. unfold aequiv in H. split.
    - intros H'. inversion H'; subst.
        remember e' as e eqn:E. rewrite E at 2.
        assert (e' = t_update e k (aeval e a)) as H0.
            { rewrite <- H. simpl. rewrite t_update_same. symmetry. assumption. }
        rewrite H0. constructor. reflexivity.
    - intros H'. inversion H'; subst. rewrite <- H. simpl. 
        rewrite t_update_same. constructor.
Qed.
    
Lemma refl_aequiv : forall (a:aexp), aequiv a a.
Proof. intros a e. reflexivity. Qed.

Lemma sym_aequiv : forall (a b:aexp), aequiv a b -> aequiv b a.
Proof. intros a b H e. symmetry. apply H. Qed.

Lemma trans_aequiv : forall (a b c:aexp), aequiv a b -> aequiv b c -> aequiv a c.
Proof.
    intros a b c Eab Ebc e. apply eq_trans with (aeval e b).
    - apply Eab.
    - apply Ebc.
Qed.

Lemma refl_bequiv : forall (b:bexp), bequiv b b.
Proof. intros b e. reflexivity. Qed.

Lemma sym_bequiv : forall (a b:bexp), bequiv a b -> bequiv b a.
Proof. intros a b H e. symmetry. apply H. Qed.

Lemma trans_bequiv : forall (a b c:bexp), bequiv a b -> bequiv b c -> bequiv a c.
Proof.
    intros a b c Eab Ebc e. apply eq_trans with (beval e b).
    - apply Eab.
    - apply Ebc.
Qed.

Lemma refl_cequiv : forall (c:com), cequiv c c.
Proof. intros c e e'. reflexivity. Qed.

Lemma sym_cequiv : forall (c d:com), cequiv c d -> cequiv d c.
Proof. intros c d H e e'. symmetry. apply H. Qed.

Lemma trans_cequiv : forall (b c d:com), cequiv b c -> cequiv c d -> cequiv b d.
Proof.
    intros b c d Ebc Ecd e e'.
    destruct (Ecd e e') as [H1 H2]. 
    destruct (Ebc e e') as [H3 H4].
    split.
    - intros H. apply H1, H3, H. 
    - intros H. apply H4, H2, H.
Qed.

Lemma CAss_congruence : forall (k:Key) (a a':aexp),
    aequiv a a' -> cequiv (k ::= a) (k ::= a').
Proof.
    intros k a a' H e e'. split.
    - intros H'. inversion H'; subst. constructor. symmetry. apply H.
    - intros H'. inversion H'; subst. constructor. apply H.
Qed.

Lemma CSeq_congruence : forall (c1 c1' c2 c2':com),
    cequiv c1 c1' -> cequiv c2 c2' -> cequiv (c1;;c2) (c1';;c2').
Proof.
    intros c1 c1' c2 c2' H1 H2 e e'. split.
    - intros H. inversion H. subst. apply E_Seq with e'0.
        + apply H1. assumption.
        + apply H2. assumption.
    - intros H. inversion H; subst. apply E_Seq with e'0.
        + apply H1. assumption.
        + apply H2. assumption.
Qed.

Lemma CIf_congruence : forall (b b':bexp) (c1 c1' c2 c2':com),
    bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' -> 
    cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
    intros b b' c1 c1' c2 c2' H H1 H2 e e'. split.
    - intros H'. inversion H'; subst.
        + apply E_IfTrue.
            { rewrite <- H. assumption. }
            { rewrite <- (H1 e). assumption. }
        + apply E_IfFalse.
            { rewrite <- H. assumption. }
            { rewrite <- (H2 e). assumption. }
    - intros H'. inversion H'; subst.
        + apply E_IfTrue.
            { rewrite H. assumption. }
            { rewrite (H1 e). assumption. }
        + apply E_IfFalse.
            { rewrite H. assumption. }
            { rewrite (H2 e). assumption. }
Qed.

Lemma CWhile_congruence : forall (b b':bexp) (c1 c1':com),
    bequiv b b'-> cequiv c1 c1' -> 
    cequiv (WHILE b DO c1 END) (WHILE b' DO c1' END).
Proof.
    intros b b' c1 c1' H H1 e e'. split.
    - intros H'. remember (WHILE b DO c1 END) as c eqn:E.
        revert E H H1. induction H'; try (intros H0; inversion H0).
        + subst. intros Hb H1. apply E_WhileEnd. rewrite <- Hb. assumption.
        + subst. intros Hb H1. apply E_WhileLoop with e'.
            { rewrite <- Hb. assumption. }
            { rewrite <- (H1 e). assumption. }
            { apply IHH'2.
                { reflexivity. }
                { assumption. }
                { assumption. } 
            }
    - intros H'. remember (WHILE b' DO c1' END) as c' eqn:E'.
        revert E' H H1. induction H'; try (intros H0; inversion H0).
        + subst. intros Hb H1. apply E_WhileEnd. rewrite Hb. assumption.
        + subst. intros Hb H1. apply E_WhileLoop with e'. 
            { rewrite Hb. assumption. }
            { rewrite (H1 e). assumption. }
            { apply IHH'2.
                { reflexivity. }
                { assumption. }
                { assumption. }
            }
Qed.


Lemma CSeq_Assign_Num : forall (k1 k2:Key) (n:nat),
    cequiv (k1 ::= ANum n ;; k2 ::= AKey k1) (k1 ::= ANum n ;; k2 ::= ANum n).
Proof.
    intros k1 k2 n e e'. split.
    - remember (k1 ::= ANum n) as c1 eqn:E1.
      remember (k2 ::= AKey k1) as c2 eqn:E2.
      remember (c1 ;; c2) as c eqn:E. intros H. revert c1 c2 E1 E2 E. 
      induction H; intros c3 c4 E1 E2 E; inversion E; subst.
        + clear E IHceval1 IHceval2. apply E_Seq with e'.
            { assumption. }
            { assert (e' = t_update e k1 n) as H1.
              apply (ceval_deterministic (k1 ::= ANum n) e). 
                { assumption. }
                { constructor. reflexivity. }
                { assert (e'' = t_update e' k2 n) as H2.
                    { apply (ceval_deterministic (k2 ::= AKey k1) e').
                        { assumption. }
                        { constructor. rewrite H1. simpl. apply t_update_eq. }
                    }
                  rewrite H2. constructor. rewrite H1. reflexivity.
                }
            }
    - remember (k1 ::= ANum n) as c1 eqn:E1.
      remember (k2 ::= ANum n) as c2 eqn:E2.
      remember (c1 ;; c2) as c eqn:E. intros H. revert c1 c2 E1 E2 E. 
      induction H; intros c3 c4 E1 E2 E; inversion E; subst.
        + clear E IHceval1 IHceval2. apply E_Seq with e'.
            { assumption. }
            { assert (e' = t_update e k1 n) as H1.
                apply (ceval_deterministic (k1 ::= ANum n) e).
                    { assumption. }
                    { constructor. reflexivity. }
                    { assert (e'' = t_update e' k2 n) as H2.
                        { apply (ceval_deterministic (k2 ::= ANum n) e').
                            { assumption. }
                            { constructor. reflexivity. }
                        }
                        rewrite H2. constructor. rewrite H1. 
                        simpl. apply t_update_eq.
                    }
            }
Qed.
               

Lemma CSeq_Assign_Key : forall (k1 k2 k:Key),
    cequiv (k1 ::= AKey k ;; k2 ::= AKey k1) (k1 ::= AKey k ;; k2 ::= AKey k).
Proof.
    intros k1 k2 k e e'. split.
    - remember (k1 ::= AKey k) as c1 eqn:E1.
      remember (k2 ::= AKey k1) as c2 eqn:E2.
      remember (c1 ;; c2) as c eqn:E. intros H. revert c1 c2 E1 E2 E.
      induction H; intros c3 c4 E1 E2 E; inversion E; subst.
        + clear E IHceval1 IHceval2. apply E_Seq with e'.
            { assumption. }
            { assert (e' = t_update e k1 (e k)) as H1.
                { apply (ceval_deterministic (k1 ::= AKey k) e).
                    { assumption.  }
                    { constructor. reflexivity. }
                }
              assert (e'' = t_update e' k2 (aeval e' (AKey k1))) as H2.
                { apply (ceval_deterministic (k2 ::= AKey k1) e').
                    { assumption. }
                    { constructor. reflexivity. }
                }
              rewrite H2. constructor. rewrite H1. simpl.
              rewrite (t_update_eq nat e k1 (e k)).  
              apply t_update_irrel.
            }
    - remember (k1 ::= AKey k) as c1 eqn:E1.
      remember (k2 ::= AKey k) as c2 eqn:E2.
      remember (c1 ;; c2) as c eqn:E. intros H. revert c1 c2 E1 E2 E.
      induction H; intros c3 c4 E1 E2 E; inversion E; subst.
        + clear E IHceval1 IHceval2. apply E_Seq with e'.
            { assumption. }
            { assert (e' = t_update e k1 (e k)) as H1.
                { apply (ceval_deterministic (k1 ::= AKey k) e).
                    { assumption. }
                    { constructor. reflexivity. }
                } 
              assert (e'' = t_update e' k2 (e' k)) as H2.
                { apply (ceval_deterministic (k2 ::= AKey k) e').
                    { assumption. }
                    { constructor. reflexivity. }
                }
              rewrite H2. constructor. rewrite H1. simpl.
              rewrite (t_update_eq nat e k1 (e k)). symmetry.
              apply t_update_irrel.
            }
Qed.
