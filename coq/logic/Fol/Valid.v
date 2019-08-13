Require Import List.

Require Import Eq.
Require Import Map.
Require Import Remove.
Require Import Injective.

Require Import Fol.P.
Require Import Fol.Free.
Require Import Fol.Variable.
Require Import Fol.Subformula.

Definition valid (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (q:P v) : Prop :=
    forall (p:P v) (x:v), p <<= q -> 
        In x (free e p) -> In (f x) (free e' (fmap f p)).

Arguments valid {v} {w} _ _ _ _.

(* f is valid for q iff it is valid for every sub-formula of q                  *)
Lemma valid_sub : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (q:P v),
    valid e e' f q <-> forall (p:P v), p <<= q -> valid e e' f p.    
Proof.
    intros v w e e' f q. split.
    - intros H p H1. unfold valid. intros o x H2 H3. apply H.
        + apply Sub_tran with p; assumption.
        + assumption.
    - intros H. apply H. apply Sub_refl.
Qed.

Lemma valid_bot : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w),
    valid e e' f Bot.
Proof.
    unfold valid. intros v w e e' f s y H1 H2. destruct H1 as [H1|H1].
    - subst. simpl. inversion H2.
    - inversion H1.
Qed.


Lemma valid_elem : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (x y:v),
    valid e e' f (Elem x y).
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
    valid e e' f (Imp p1 p2) <-> valid e e' f p1 /\ valid e e' f p2.
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
    valid e e' f (All x p1) <->  
    valid e e' f p1 /\  
    forall (y:v), In y (free e (All x p1)) -> f x <> f y.
Proof.
    intros v w e e' f p1 x. split.
    - intros H. split.
        + apply (valid_sub v w e e' f (All x p1)). 
            { assumption. }
            { right. apply Sub_refl. }
        + intros y H1 H2. 
            assert (In (f y) (free e' (fmap f (All x p1)))) as H3.
                { apply H.
                    { apply Sub_refl. }
                    { assumption. }
                }
            assert (~In (f x) (free e' (fmap f (All x p1)))) as H4.
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
    valid e e' f q <-> forall (p:P v), p <<= q -> 
        free e' (fmap f p) = map f (free e p).
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
                    assert (~In (f x) (free e' (All (f x) (fmap f p1)))) as Ex.
                        { simpl. apply remove_x_gone. }
                    assert (In (f y) (free e' (All (f x) (fmap f p1)))) as Ey. 
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
            { apply IH1. intros p H'. apply H. apply Sub_tran with p1.
                { assumption. }
                { right. apply Sub_refl. }
            }
            { intros y H1 H2.
              assert (~In (f x) (free e' (fmap f (All x p1)))) as Ex.
                { simpl. apply remove_x_gone. }
              assert (In (f y) (free e' (fmap f (All x p1)))) as Ey. 
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

Lemma valid_inj : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (q:P v),
    injective_on (var q) f -> valid e e' f q.
Proof.
    intros v w e e' f q H. apply valid_free. intros p H'. apply free_inj.
    apply injective_on_incl with (var q).
    - apply Sub_var. assumption.
    - assumption.
Qed.

