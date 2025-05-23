Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Func.Replace.
Require Import Logic.Func.Permute.
Require Import Logic.Func.Composition.

Require Import Logic.List.In.
Require Import Logic.List.Remove.
Require Import Logic.List.Replace.
Require Import Logic.List.Include.
Require Import Logic.List.Coincide.
Require Import Logic.List.InjectiveOn.

Require Import Logic.Lam.Free.
Require Import Logic.Lam.Bound.
Require Import Logic.Lam.Syntax.
Require Import Logic.Lam.Functor.
Require Import Logic.Lam.Variable.
Require Import Logic.Lam.Subformula.

Definition valid (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v) : Prop :=
    forall (s:T v) (x:v), s <<= t -> 
        x :: Fr s -> f x :: Fr (fmap f s).

Arguments valid {v} {w} {e} {e'} _ _.

(* f is valid for t iff it is valid for every sub-term of t                     *)
Lemma valid_sub : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    valid f t <-> forall (s:T v), s <<= t -> valid f s.    
Proof.
    intros v w e e' f t. split.
    - intros H s H1. unfold valid. intros r x H2 H3. apply H.
        + apply Sub_tran with s; assumption.
        + assumption.
    - intros H. apply H. apply Sub_refl.
Qed.

Lemma valid_var : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (x:v),
    valid f (Var x).
Proof.
    unfold valid. intros v w e e' f x s y H1 H2. destruct H1 as [H1|H1].
    - subst. simpl. left. destruct H2 as [H2|H2].
        + subst. reflexivity.
        + inversion H2.
    - inversion H1.
Qed.

Lemma valid_app : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t1 t2:T v),
    valid f (App t1 t2) <-> valid f t1 /\ valid f t2.
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
    valid f (Lam x t1) <->  
    valid f t1 /\  
    forall (y:v), y :: Fr (Lam x t1) -> f x <> f y.
Proof.
    intros v w e e' f t1 x. split.
    - intros H. split.
        + apply (valid_sub v w e e' f (Lam x t1)). 
            { assumption. }
            { right. apply Sub_refl. }
        + intros y H1 H2. 
            assert (f y :: Fr (fmap f (Lam x t1))) as H3.
                { apply H.
                    { apply Sub_refl. }
                    { assumption. }
                }
            assert (~ f x :: Fr (fmap f (Lam x t1))) as H4.
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
    valid f t <-> forall (s:T v), s <<= t -> Fr (fmap f s) = map f (Fr s).
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
                    assert (~ f x :: Fr (Lam (f x) (fmap f t1))) as Ex.
                        { simpl. apply remove_x_gone. }
                    assert (f y :: Fr (Lam (f x) (fmap f t1))) as Ey. 
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
            { apply IH1.  intros s H'. apply H. right. assumption. }
            { intros y H1 H2.
              assert (~ f x :: Fr (fmap f (Lam x t1))) as Ex.
                { simpl. apply remove_x_gone. }
              assert (f y :: Fr (fmap f (Lam x t1))) as Ey. 
                { rewrite H.
                    { apply in_map_iff. exists y. split.
                        { reflexivity. }
                        { assumption. }}
                    { left. reflexivity. }}
              rewrite <- H2 in Ey. apply Ex. assumption. }
Qed.

Lemma valid_inj : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    injective_on (var t) f -> valid f t.
Proof.
    intros v w e e' f t H. apply valid_free. intros s H'. apply free_inj.
    apply injective_on_incl with (var t).
    - apply Sub_var. assumption.
    - assumption.
Qed.


Lemma valid_charac : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    valid f t <-> forall (t1:T v) (x y:v), 
        (Lam x t1) <<= t -> y :: Fr (Lam x t1) -> f x <> f y.
Proof.
    intros v w e e' f t. split.
    - intros H t1 x y H1 H2 H3.
      assert (f y :: Fr (fmap f (Lam x t1))) as H4.
        { apply H; assumption. }
      assert (~ f x :: Fr (fmap f (Lam x t1))) as H5.
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
    ~ y :: var t -> valid (y // x) t.
Proof.
    intros v e x y t H. apply valid_inj. apply replace_inj. assumption.
Qed.


Lemma valid_compose : forall (u v w:Type) (e:Eq u) (e':Eq v) (e'':Eq w),
    forall (f:u -> v) (g:v -> w) (t:T u),
    (valid f t) /\ (valid g (fmap f t)) <-> valid (g;f) t.
Proof.
    intros u v w e e' e'' f g t. split.
    - intros [Hf Hg]. apply valid_free. intros s H.
      rewrite fmap_comp. unfold comp. 
      rewrite valid_free in Hg. rewrite Hg.
        + rewrite valid_free in Hf. rewrite Hf.
            { rewrite map_map. reflexivity. }
            { assumption. }
        + rewrite Sub_fmap. apply in_map_iff. 
          exists s. split.
            { reflexivity. }
            { assumption. }
    - intros H. assert (valid f t) as H'.
        { revert H. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros H.
            + apply valid_var.
            + apply valid_app. apply valid_app in H. destruct H as [H1 H2]. split.
                { apply IH1. assumption. }
                { apply IH2. assumption. }
            + apply valid_lam. apply valid_lam in H. destruct H as [H1 H2]. split. 
                { apply IH1. assumption. }
                { intros y H3 H4. apply (H2 y H3). 
                  unfold comp. rewrite H4. reflexivity.
                }
        }
      split.
        + assumption.
        + apply valid_free. intros s' H1. 
          rewrite Sub_fmap in H1.
          rewrite in_map_iff in H1. destruct H1 as [s [H1 H2]].
          rewrite <- H1. fold (comp (fmap g) (fmap f) s). 
          rewrite <- fmap_comp. rewrite valid_free in H. 
          rewrite H.
            { unfold comp. rewrite <- map_map. rewrite valid_free in H'. 
              rewrite H'.
                { reflexivity. }
                { assumption. }
            }
            { assumption. }
Qed.


Lemma valid_fmap : forall (v w:Type) (e:Eq v) (e':Eq w) (f g:v -> w) (t:T v),
    (fmap f t) = (fmap g t) -> valid f t -> valid g t.
Proof.
    intros v w e e' f g t H H' s x H1 H2. apply var_support in H.
    assert (f x = g x) as H3.
        { apply (coincide_incl v w f g (var t) (var s)).
            { apply Sub_var. assumption. }
            { assumption. }
            { apply (free_var v e s). assumption. }
        }
    assert (fmap f s = fmap g s) as H4.
        { apply var_support. apply coincide_incl with (var t).    
            { apply Sub_var. assumption. }
            { assumption. }
        }
    rewrite <- H3, <- H4. apply H'; assumption.
Qed.


Lemma valid_bnd : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    (exists (xs:list v), 
        bnd t <= xs /\
        injective_on xs f /\
        (forall (x y:v), x :: xs -> y :: var t -> ~ y :: xs -> f x <> f y))
        -> valid f t.
Proof.
    intros v w e e' f t [xs [H1 [H2 H3]]]. apply valid_charac.
    intros t1 x y H4 H5. 
    assert (x :: xs) as H0. 
        { apply H1. apply Sub_bnd in H4. apply H4. left. reflexivity. }
    destruct (in_dec eqDec y xs) as [H6|H6].
    - intros H7. simpl in H5. apply remove_charac in H5.
      destruct H5 as [_ H5]. apply H5. apply H2; assumption.
    - apply H3.
        + assumption.
        + apply Sub_var in H4. apply H4. apply (free_var v e). assumption.
        + assumption.
Qed.

(* valid defined as an inductive predicate.                                     *)
Inductive valid' (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) : T v -> Prop :=
| VVar  : forall (x:v), valid' v w e e' f (Var x)
| VApp  : forall (t1 t2:T v), 
    valid' v w e e' f t1 -> 
    valid' v w e e' f t2 -> 
    valid' v w e e' f (App t1 t2)
| VLam : forall (x:v) (t1:T v),
    valid' v w e e' f t1 ->
    (forall (y:v), y :: Fr (Lam x t1) -> f x <> f y) ->
    valid' v w e e' f (Lam x t1)
.

Arguments valid' {v} {w} {e} {e'}.

Lemma valid_equivalence : forall (v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(t:T v),
    valid f t <-> valid' f t.
Proof.
    intros v w e e' f t. split.
    - induction t as [x|t1 IH1 t2 IH2|x t1 IH1].
        + intros _. constructor. 
        + intros H. apply valid_app in H. destruct H as [H1 H2]. constructor.
            { apply IH1. assumption. }
            { apply IH2. assumption. }
        + intros H. apply valid_lam in H.  destruct H as [H1 H2]. constructor.
            { apply IH1. assumption. }
            { assumption. }
    - intros H. induction H as [x|t1 t2 H1 IH1 H2 IH2|x t1 H1 IH1 H2].
        + apply valid_var.
        + apply valid_app. split; assumption.
        + apply valid_lam. split; assumption.
Qed.

Lemma valid_permute : forall (v:Type) (e:Eq v) (x y:v) (t:T v), 
  valid (y <:> x) t.
Proof.
  intros v e x y t.
  apply valid_inj, injective_injective_on,permute_injective.
Qed.
