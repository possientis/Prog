Require Import List.

Require Import Eq.
Require Import Map.
Require Import Remove.
Require Import Replace.
Require Import Injective.
Require Import Composition.

Require Import Lam.T.
Require Import Lam.Free.
Require Import Lam.Variable.
Require Import Lam.Subformula.

Definition valid (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v) : Prop :=
    forall (s:T v) (x:v), s <<= t -> 
        In x (free e s) -> In (f x) (free e' (fmap f s)).

Arguments valid {v} {w} _ _ _ _.

(* f is valid for t iff it is valid for every sub-term of t                     *)
Lemma valid_sub : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    valid e e' f t <-> forall (s:T v), s <<= t -> valid e e' f s.    
Proof.
    intros v w e e' f t. split.
    - intros H s H1. unfold valid. intros r x H2 H3. apply H.
        + apply Sub_tran with s; assumption.
        + assumption.
    - intros H. apply H. apply Sub_refl.
Qed.

Lemma valid_var : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (x:v),
    valid e e' f (Var x).
Proof.
    unfold valid. intros v w e e' f x s y H1 H2. destruct H1 as [H1|H1].
    - subst. simpl. left. destruct H2 as [H2|H2].
        + subst. reflexivity.
        + inversion H2.
    - inversion H1.
Qed.

Lemma valid_app : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t1 t2:T v),
    valid e e' f (App t1 t2) <-> valid e e' f t1 /\ valid e e' f t2.
Proof.
    intros v w e e' f t1 t2. split.
    - intros H. split; apply (valid_sub v w e e' f (App t1 t2)). 
        + assumption.
        + right. apply in_or_app. left. apply Sub_refl.
        + assumption.
        + right. apply in_or_app. right. apply Sub_refl.
    - intros [H1 H2] s x [H|H].
        + subst. simpl. intros H.
          apply in_or_app. apply in_app_or in H.
          destruct H as [H|H]. 
            { left.  revert H. apply H1. apply Sub_refl. }
            { right. revert H. apply H2. apply Sub_refl. }
        + apply in_app_or in H. destruct H as [H|H].
            { apply H1. assumption. }
            { apply H2. assumption. }
Qed.


Lemma valid_lam : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t1:T v) (x:v),
    valid e e' f (Lam x t1) <->  
    valid e e' f t1 /\  
    forall (y:v), In y (free e (Lam x t1)) -> f x <> f y.
Proof.
    intros v w e e' f t1 x. split.
    - intros H. split.
        + apply (valid_sub v w e e' f (Lam x t1)). 
            { assumption. }
            { right. apply Sub_refl. }
        + intros y H1 H2. 
            assert (In (f y) (free e' (fmap f (Lam x t1)))) as H3.
                { apply H.
                    { apply Sub_refl. }
                    { assumption. }
                }
            assert (~In (f x) (free e' (fmap f (Lam x t1)))) as H4.
                { simpl. apply remove_x_gone. }
            apply H4. rewrite H2. assumption.
    - intros [H1 H2] s y H3 H4. destruct H3 as [H3|H3].
        + subst. simpl. apply remove_charac. split.
            { apply H1.
                { apply Sub_refl. }
                { simpl in H4. apply remove_charac in H4. 
                  destruct H4. assumption.  
                }
            }
            { apply H2. assumption. }
        + apply H1; assumption.
Qed.

(* We cannot follow the set theoretic proof as this is a stronger result,       *)
(* due to the order being preserved in lists. Structural induction on t.        *)
Lemma valid_free : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    valid e e' f t <-> forall (s:T v), s <<= t -> 
        free e' (fmap f s) = map f (free e s).
Proof.
    intros v w e e' f t. split.
    - induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl; intros H s H'.
        + destruct H' as [H'|H'].
            { subst. reflexivity. }
            { inversion H'. }
        + destruct H' as [H'|H'].
            { subst. simpl. rewrite map_app. rewrite IH1, IH2.
                { reflexivity. }
                { apply valid_sub with (App t1 t2).
                    { assumption. }
                    { right. apply in_or_app. right. apply Sub_refl. }
                }
                { apply Sub_refl. }
                { apply valid_sub with (App t1 t2). 
                    { assumption. }
                    { right. apply in_or_app. left. apply Sub_refl. }
                }
                { apply Sub_refl. }
            }
            { apply in_app_or in H'. destruct H' as [H'|H'].
                { apply IH1.
                    { apply valid_sub with (App t1 t2).
                        { assumption. }
                        { right. apply in_or_app. left. apply Sub_refl. }
                    }
                    { assumption. }
                }
                { apply IH2.
                    { apply valid_sub with (App t1 t2).
                        { assumption. }
                        { right. apply in_or_app. right. apply Sub_refl. }
                    }
                    { assumption. }
                }
            }
        + destruct H' as [H'|H'].
            { subst. simpl. rewrite IH1.
                { apply remove_map. intros y H1 H2 H3.
                    assert (~In (f x) (free e' (Lam (f x) (fmap f t1)))) as Ex.
                        { simpl. apply remove_x_gone. }
                    assert (In (f y) (free e' (Lam (f x) (fmap f t1)))) as Ey. 
                        { unfold valid in H. apply (H (Lam x t1) y). 
                            { apply Sub_refl. }
                            { simpl. apply remove_charac. split; assumption. }
                        }
                    rewrite <- H3 in Ey. apply Ex. assumption.  
                }
                apply (valid_sub v w e e' f (Lam x t1)).
                    { assumption. }
                    { right. apply Sub_refl. }
                    { apply Sub_refl. }
            }
            { apply IH1.
                { apply (valid_sub v w e e' f (Lam x t1)).
                    { assumption. }
                    { right. apply Sub_refl. }
                }
                { assumption. }
            } 
    - induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl; intros H.
        + apply valid_var.
        + apply valid_app. split.
            { apply IH1. intros s H'. apply H. right. 
              apply in_or_app. left. assumption. }
            { apply IH2. intros s H'. apply H. right.
              apply in_or_app. right. assumption. } 
        + apply valid_lam. split.
            { apply IH1. intros s H'. apply H. apply Sub_tran with t1.
                { assumption. }
                { right. apply Sub_refl. }
            }
            { intros y H1 H2.
              assert (~In (f x) (free e' (fmap f (Lam x t1)))) as Ex.
                { simpl. apply remove_x_gone. }
              assert (In (f y) (free e' (fmap f (Lam x t1)))) as Ey. 
                { rewrite H.
                    { apply mapIn. exists y. split.
                        { assumption. }
                        { reflexivity. }
                    }
                    { apply Sub_refl. }
                }
              rewrite <- H2 in Ey. apply Ex. assumption. 
            }
Qed.

Lemma valid_inj : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    injective_on (var t) f -> valid e e' f t.
Proof.
    intros v w e e' f t H. apply valid_free. intros s H'. apply free_inj.
    apply injective_on_incl with (var t).
    - apply Sub_var. assumption.
    - assumption.
Qed.


Lemma valid_charac : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    valid e e' f t <-> forall (t1:T v) (x y:v), 
        (Lam x t1) <<= t -> In y (free e (Lam x t1)) -> f x <> f y.
Proof.
    intros v w e e' f t. split.
    - intros H t1 x y H1 H2 H3.
      assert (In (f y) (free e' (fmap f (Lam x t1)))) as H4.
        { apply H; assumption. }
      assert (~In (f x) (free e' (fmap f (Lam x t1)))) as H5.
        { simpl. apply remove_x_gone. }
      rewrite <- H3 in H4. apply H5. assumption.
    - induction t as [z|t1' IH1 t2' IH2|z t1' IH1]; intros H.
        + apply valid_var.
        + apply valid_app. split.
            { apply IH1. intros t1 x y H1. apply H. apply Sub_tran with t1'.
                { assumption. }
                { right. apply in_or_app. left. apply Sub_refl. }
            }
            { apply IH2. intros t1 x y H1. apply H. apply Sub_tran with t2'.
                { assumption. }
                { right. apply in_or_app. right. apply Sub_refl. }
            }
        + apply valid_lam. split.
            { apply IH1. intros t1 x y H1. apply H. apply Sub_tran with t1'.
                { assumption. }
                { right. apply Sub_refl. }
            }
            { intros y H1. apply H with t1'.
                { apply Sub_refl. }
                { assumption. }
            }
Qed.

Lemma valid_replace : forall (v:Type) (e:Eq v) (x y:v) (t:T v),
    ~In y (var t) -> valid e e (replace e x y) t.
Proof.
    intros v e x y t H. apply valid_inj. apply replace_inj. assumption.
Qed.

(*
Lemma valid_compose : forall (u v w:Type) (e:Eq u) (e':Eq v) (e'':Eq w),
    forall (f:u -> v) (g:v -> w) (t:T u),
    (valid e e' f t) /\ (valid e' e'' g (fmap f t)) <-> valid e e'' (g;f) t.
Proof.
    intros u v w e e' e'' f g t. split.
    - intros [Hf Hg]. apply valid_free. intros s H.
      rewrite fmap_comp. unfold comp. 
      rewrite valid_free in Hg. rewrite Hg.
      + rewrite valid_free in Hf. rewrite Hf.
        { rewrite map_map. reflexivity. }
        { assumption. }
      + unfold isSubFormulaOf. rewrite Sub_fmap. apply mapIn.   
        exists s. split.
            { assumption. }
            { reflexivity. }
    -
        
Show.
*)


