Require Import List.

Require Import Eq.
Require Import Remove.

Require Import Lam.T.
Require Import Lam.Free.
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


(*
(* We cannot follow set theoretic proof as this is a stronger result, due to    *)
(* the order being preserved in lists. Structural induction on t                *)
Lemma valid_free : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    valid e e' f t <-> forall (s:T v), s <<= t -> free e' (fmap f s) = map f (free e s).
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
Show.
*)
