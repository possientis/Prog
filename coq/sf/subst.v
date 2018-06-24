Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import dictionary.
Require Import equiv.
Require Import state.

Fixpoint subst_aexp (k:Key)(u:aexp)(a:aexp) : aexp :=
    match a with
    | ANum n        => ANum n
    | AKey k'       => if beq_Key k k' then u else AKey k'
    | APlus  a1 a2  => APlus  (subst_aexp k u a1) (subst_aexp k u a2)
    | AMinus a1 a2  => AMinus (subst_aexp k u a1) (subst_aexp k u a2)
    | AMult  a1 a2  => AMult  (subst_aexp k u a1) (subst_aexp k u a2)
    end.


Definition subst_equiv_property := forall (k1 k2:Key) (a1 a2:aexp),
    cequiv (k1 ::= a1 ;; k2 ::= a2) (k1 ::= a1 ;; k2 ::= subst_aexp k1 a1 a2).

Theorem subst_inequiv : ~subst_equiv_property.
Proof.
    unfold subst_equiv_property. intros H.
    remember (x ::= APlus (AKey x) (ANum 1) ;; 
              y ::= AKey x) as c1 eqn:C1.
    remember (x ::= APlus (AKey x) (ANum 1) ;; 
              y ::= APlus (AKey x) (ANum 1)) as c2 eqn:C2.
    assert (cequiv c1 c2) as H'. { subst. apply H. } clear H.
    unfold cequiv in H'.
    remember emptyState as e1 eqn:E1.
    remember (t_update (t_update e1 x 1) y 1) as e2 eqn:E2.
    remember (t_update (t_update e1 x 1) y 2) as e3 eqn:E3.
    remember (t_update e1 x 1) as e' eqn:E'.
    destruct (H' e1 e2) as [H _]. clear H'. 
    assert (ceval c1 e1 e2) as H'.
        { rewrite C1. apply E_Seq with e'. 
            - rewrite E'. constructor. simpl. rewrite E1. reflexivity.
            - rewrite E2. constructor. simpl. rewrite E'. reflexivity.
        }
    apply H in H'. clear H. rename H' into H. 
    assert (ceval c2 e1 e3) as H'.
        { rewrite C2. apply E_Seq with e'.
            - rewrite E'. constructor. simpl. rewrite E1. reflexivity.
            - rewrite E3. constructor. simpl. rewrite E'. reflexivity.
        }
    assert (e2 = e3) as E. { apply (ceval_deterministic c2 e1); assumption. }
    assert (1 = 2) as Contra. 
        { assert (aeval e2 (AKey y) = 1) as K1.
            { simpl. rewrite E2. reflexivity. }
          assert (aeval e3 (AKey y) = 2) as K2.
            { simpl. rewrite E3. reflexivity. }
          rewrite <- K1 at 1. rewrite <- K2. rewrite E. reflexivity. 
        }
    inversion Contra.
Qed.

Inductive var_not_used_in_aexp (k:Key) : aexp -> Prop :=
| VNUNum: forall (n:nat), var_not_used_in_aexp k (ANum n)
| VNUKey: forall (k':Key), k <> k' -> var_not_used_in_aexp k (AKey k') 
| VNUPlus : forall (a1 a2:aexp), 
    var_not_used_in_aexp k a1 ->
    var_not_used_in_aexp k a2 ->
    var_not_used_in_aexp k (APlus a1 a2)
| VNUMinus : forall (a1 a2:aexp), 
    var_not_used_in_aexp k a1 ->
    var_not_used_in_aexp k a2 ->
    var_not_used_in_aexp k (AMinus a1 a2)
| VNUMult : forall (a1 a2:aexp), 
    var_not_used_in_aexp k a1 ->
    var_not_used_in_aexp k a2 ->
    var_not_used_in_aexp k (AMult a1 a2)
.


Lemma aeval_weakening : forall (k:Key) (e:State) (a:aexp) (n:nat),
    var_not_used_in_aexp k a -> aeval (t_update e k n) a = aeval e a.
Proof.
    intros k e a n H. revert e n. 
    induction H as  [ m
                    |k'
                    |a1 a2 H1 IH1 H2 IH2
                    |a1 a2 H1 IH1 H2 IH2
                    |a1 a2 H1 IH1 H2 IH2
                    ]; 
    intros e n; simpl.
    - reflexivity. 
    - apply t_update_neq. assumption. 
    - rewrite (IH1 e n), (IH2 e n). reflexivity.
    - rewrite (IH1 e n), (IH2 e n). reflexivity.
    - rewrite (IH1 e n), (IH2 e n). reflexivity.
Qed.

(*
Lemma subst_equivalence : forall (k1 k2:Key) (a1 a2:aexp),
    var_not_used_in_aexp k1 a1 -> 
    cequiv (k1 ::= a1 ;; k2 ::= a2) (k1 ::= a1 ;; k2 ::= subst_aexp k1 a1 a2).
Proof.
    intros k1 k2 a1 a2 H. revert k2 a2.
    induction H as  [ m
                    |k'
                    |a1 a1' H1 IH1 H2 IH2
                    |a1 a1' H1 IH1 H2 IH2
                    |a1 a1' H1 IH1 H2 IH2
                    ];
    intros k a2; simpl; induction a2; simpl.
    - apply refl_cequiv.
    - destruct (beq_Key k1 k0) eqn:E. 
        + apply beq_Key_true_iff in E. rewrite <- E. apply CSeq_Assign.
        + apply refl_cequiv.
         
    -
Show.

*) 

