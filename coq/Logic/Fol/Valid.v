Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Func.Replace.
Require Import Logic.Func.Composition.

Require Import Logic.List.In.
Require Import Logic.List.Remove.
Require Import Logic.List.Replace.
Require Import Logic.List.Include.
Require Import Logic.List.Coincide.
Require Import Logic.List.InjectiveOn.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Bound.
Require Import Logic.Fol.Syntax.
Require Import Logic.Fol.Functor.
Require Import Logic.Fol.Variable.
Require Import Logic.Fol.Subformula.

Definition valid (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (q:P v) : Prop :=
    forall (p:P v) (x:v), p <<= q -> 
        x :: Fr p -> f x :: Fr (fmap f p).

Arguments valid {v} {w} {e} {e'} _ _.

(* f is valid for q iff it is valid for every sub-formula of q                  *)
Lemma valid_sub : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (q:P v),
    valid f q <-> forall (p:P v), p <<= q -> valid f p.    
Proof.
    intros v w e e' f q. split.
    - intros H p H1. unfold valid. intros o x H2 H3. apply H.
        + apply Sub_tran with p; assumption.
        + assumption.
    - intros H. apply H. apply Sub_refl.
Qed.

Lemma valid_bot : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w),
    valid f Bot.
Proof.
    unfold valid. intros v w e e' f s y H1 H2. destruct H1 as [H1|H1].
    - subst. simpl. inversion H2.
    - inversion H1.
Qed.


Lemma valid_elem : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (x y:v),
    valid f (Elem x y).
Proof.
    unfold valid. intros v w e e' f x y s z H1 H2. destruct H1 as [H1|H1].
    - subst. simpl. destruct H2 as [H2|H2].
        + subst. left. reflexivity.
        + destruct H2 as [H2|H2].
            { subst. right. left. reflexivity. }
            { inversion H2. }
    - inversion H1.
Qed.

Lemma valid_imp : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (p1 p2:P v),
    valid f (Imp p1 p2) <-> valid f p1 /\ valid f p2.
Proof.
    intros v w e e' f p1 p2. split.
    - intros H. split; apply (valid_sub v w e e' f (Imp p1 p2)). 
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

Lemma valid_all : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (p1:P v) (x:v),
    valid f (All x p1) <->  
    valid f p1 /\  
    forall (y:v), y :: Fr (All x p1) -> f x <> f y.
Proof.
    intros v w e e' f p1 x. split.
    - intros H. split.
        + apply (valid_sub v w e e' f (All x p1)). 
            { assumption. }
            { right. apply Sub_refl. }
        + intros y H1 H2. 
            assert (f y :: Fr (fmap f (All x p1))) as H3.
                { apply H.
                    { apply Sub_refl. }
                    { assumption. }
                }
            assert (~ f x :: Fr (fmap f (All x p1))) as H4.
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
(* due to the order being preserved in lists. Structural induction on q.        *)
Lemma valid_free : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (q:P v),
    valid f q <-> forall (p:P v), p <<= q -> 
        Fr (fmap f p) = map f (Fr p).
Proof.
    intros v w e e' f q. split.
    - induction q as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl; intros H p H'.
        + destruct H' as [H'|H'].
            { subst. reflexivity. }
            { inversion H'. }
        + destruct H' as [H'|H'].
            { subst. reflexivity. }
            { inversion H'. }
        + destruct H' as [H'|H'].
            { subst. simpl. rewrite map_app. rewrite IH1, IH2.
                { reflexivity. }
                { apply valid_sub with (Imp p1 p2).
                    { assumption. }
                    { right. apply in_or_app. right. apply Sub_refl. }
                }
                { apply Sub_refl. }
                { apply valid_sub with (Imp p1 p2). 
                    { assumption. }
                    { right. apply in_or_app. left. apply Sub_refl. }
                }
                { apply Sub_refl. }
            }
            { apply in_app_or in H'. destruct H' as [H'|H'].
                { apply IH1.
                    { apply valid_sub with (Imp p1 p2).
                        { assumption. }
                        { right. apply in_or_app. left. apply Sub_refl. }
                    }
                    { assumption. }
                }
                { apply IH2.
                    { apply valid_sub with (Imp p1 p2).
                        { assumption. }
                        { right. apply in_or_app. right. apply Sub_refl. }
                    }
                    { assumption. }
                }
            }
        + destruct H' as [H'|H'].
            { subst. simpl. rewrite IH1.
                { apply remove_map. intros y H1 H2 H3.
                    assert (~ f x :: Fr (All (f x) (fmap f p1))) as Ex.
                        { simpl. apply remove_x_gone. }
                    assert (f y :: Fr (All (f x) (fmap f p1))) as Ey. 
                        { unfold valid in H. apply (H (All x p1) y). 
                            { apply Sub_refl. }
                            { simpl. apply remove_charac. split; assumption. }
                        }
                    rewrite <- H3 in Ey. apply Ex. assumption.  
                }
                apply (valid_sub v w e e' f (All x p1)).
                    { assumption. }
                    { right. apply Sub_refl. }
                    { apply Sub_refl. }
            }
            { apply IH1.
                { apply (valid_sub v w e e' f (All x p1)).
                    { assumption. }
                    { right. apply Sub_refl. }
                }
                { assumption. }
            } 
    - induction q as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl; intros H.
        + apply valid_bot.
        + apply valid_elem.
        + apply valid_imp. split.
            { apply IH1. intros p H'. apply H. right. 
              apply in_or_app. left. assumption. }
            { apply IH2. intros p H'. apply H. right.
              apply in_or_app. right. assumption. } 
        + apply valid_all. split.
            { apply IH1. intros p H'. apply H. right. assumption. }
            { intros y H1 H2.
              assert (~ f x :: Fr (fmap f (All x p1))) as Ex.
                { simpl. apply remove_x_gone. }
              assert (f y :: Fr (fmap f (All x p1))) as Ey. 
                { rewrite H.
                    { apply in_map_iff. exists y. split.
                        { reflexivity. }
                        { assumption. }}
                    { left. reflexivity. }}
              rewrite <- H2 in Ey. apply Ex. assumption. }
Qed.

Lemma valid_inj : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (q:P v),
    injective_on (var q) f -> valid f q.
Proof.
    intros v w e e' f q H. apply valid_free. intros p H'. apply free_inj.
    apply injective_on_incl with (var q).
    - apply Sub_var. assumption.
    - assumption.
Qed.


Lemma valid_charac : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (p:P v),
    valid f p <-> forall (p1:P v) (x y:v), 
        (All x p1) <<= p -> y :: Fr (All x p1) -> f x <> f y.
Proof.
    intros v w e e' f t. split.
    - intros H p1 x y H1 H2 H3.
      assert (f y :: Fr (fmap f (All x p1))) as H4.
        { apply H; assumption. }
      assert (~ f x :: Fr (fmap f (All x p1))) as H5.
        { simpl. apply remove_x_gone. }
      rewrite <- H3 in H4. apply H5. assumption.
    - induction t as [|z z'|p1' IH1 p2' IH2|z p1' IH1]; intros H.
        + apply valid_bot.
        + apply valid_elem.
        + apply valid_imp. split.
            { apply IH1. intros p1 x y H1. apply H. apply Sub_tran with p1'.
                { assumption. }
                { right. apply in_or_app. left. apply Sub_refl. }
            }
            { apply IH2. intros p1 x y H1. apply H. apply Sub_tran with p2'.
                { assumption. }
                { right. apply in_or_app. right. apply Sub_refl. }
            }
        + apply valid_all. split.
            { apply IH1. intros p1 x y H1. apply H. apply Sub_tran with p1'.
                { assumption. }
                { right. apply Sub_refl. }
            }
            { intros y H1. apply H with p1'.
                { apply Sub_refl. }
                { assumption. }
            }
Qed.

Lemma valid_replace : forall (v:Type) (e:Eq v) (x y:v) (p:P v),
    ~ y :: var p -> valid (y // x) p.
Proof.
    intros v e x y p H. apply valid_inj. apply replace_inj. assumption.
Qed.

Lemma valid_compose : forall (u v w:Type) (e:Eq u) (e':Eq v) (e'':Eq w),
    forall (f:u -> v) (g:v -> w) (q:P u),
    (valid f q) /\ (valid g (fmap f q)) <-> valid (g;f) q.
Proof.
    intros u v w e e' e'' f g q. split.
    - intros [Hf Hg]. apply valid_free. intros p H.
      rewrite fmap_comp. unfold comp. 
      rewrite valid_free in Hg. rewrite Hg.
        + rewrite valid_free in Hf. rewrite Hf.
            { rewrite map_map. reflexivity. }
            { assumption. }
        + rewrite Sub_fmap. apply in_map_iff.
          exists p. split.
            { reflexivity. }
            { assumption. }
    - intros H. assert (valid f q) as H'.
        { revert H. induction q as [|x y|p1 IH1 p2 IH2|x p1 IH1]; intros H.
            + apply valid_bot.
            + apply valid_elem.
            + apply valid_imp. apply valid_imp in H. destruct H as [H1 H2]. split.
                { apply IH1. assumption. }
                { apply IH2. assumption. }
            + apply valid_all. apply valid_all in H. destruct H as [H1 H2]. split. 
                { apply IH1. assumption. }
                { intros y H3 H4. apply (H2 y H3). 
                  unfold comp. rewrite H4. reflexivity.
                }
        }
      split.
        + assumption.
        + apply valid_free. intros p' H1. 
          rewrite Sub_fmap in H1.
          rewrite in_map_iff in H1. destruct H1 as [p [H1 H2]]. 
          rewrite <- H1. fold (comp (fmap g) (fmap f) p). 
          rewrite <- fmap_comp. rewrite valid_free in H. 
          rewrite H.
            { unfold comp. rewrite <- map_map. rewrite valid_free in H'. 
              rewrite H'.
                { reflexivity. }
                { assumption. }
            }
            { assumption. }
Qed.

Lemma valid_fmap : forall (v w:Type) (e:Eq v) (e':Eq w) (f g:v -> w) (q:P v),
    (fmap f q) = (fmap g q) -> valid f q -> valid g q.
Proof.
    intros v w e e' f g q H H' p x H1 H2. apply var_support in H.
    assert (f x = g x) as H3.
        { apply (coincide_incl v w f g (var q) (var p)).
            { apply Sub_var. assumption. }
            { assumption. }
            { apply (free_var v e p). assumption. }
        }
    assert (fmap f p = fmap g p) as H4.
        { apply var_support. apply coincide_incl with (var q).    
            { apply Sub_var. assumption. }
            { assumption. }
        }
    rewrite <- H3, <- H4. apply H'; assumption.
Qed.

Lemma valid_bnd : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (q:P v),
    (exists (xs:list v), 
        bnd q <= xs /\
        injective_on xs f /\
        (forall (x y:v), x :: xs -> y :: var q -> ~ y :: xs -> f x <> f y))
        -> valid f q.
Proof.
    intros v w e e' f q [xs [H1 [H2 H3]]]. apply valid_charac.
    intros q1 x y H4 H5. 
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
Inductive valid' (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) : P v -> Prop :=
| VBot  : valid' v w e e' f Bot
| VElem : forall (x y:v), valid' v w e e' f (Elem x y)
| VImp  : forall (p1 p2:P v), 
    valid' v w e e' f p1 -> 
    valid' v w e e' f p2 -> 
    valid' v w e e' f (Imp p1 p2)
| VAll : forall (x:v) (p1:P v),
    valid' v w e e' f p1 ->
    (forall (y:v), y :: Fr (All x p1) -> f x <> f y) ->
    valid' v w e e' f (All x p1)
.

Arguments valid' {v} {w} {e} {e'}.

Lemma valid_equivalence : forall (v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(p:P v),
    valid f p <-> valid' f p.
Proof.
    intros v w e e' f p. split.
    - induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1].
        + intros _. constructor.
        + intros _. constructor. 
        + intros H. apply valid_imp in H. destruct H as [H1 H2]. constructor.
            { apply IH1. assumption. }
            { apply IH2. assumption. }
        + intros H. apply valid_all in H.  destruct H as [H1 H2]. constructor.
            { apply IH1. assumption. }
            { assumption. }
    - intros H. induction H as [|x y|p1 p2 H1 IH1 H2 IH2|x p1 H1 IH1 H2].
        + apply valid_bot.
        + apply valid_elem.
        + apply valid_imp. split; assumption.
        + apply valid_all. split; assumption.
Qed.
