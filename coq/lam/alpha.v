Require Import List.
Import ListNotations.

Require Import eq.
Require Import utils.
Require Import identity.
Require Import composition.
Require Import injective.
Require Import map.
Require Import incl.
Require Import term.
Require Import var.
Require Import inj_on_list.
Require Import permute.
Require Import inj_on_term.
Require Import remove.
Require Import vmap.
Require Import swap.
Require Import free.
Require Import adpair.



(* This inductive predicate defines alpha-equivalence           *)
(* There are four ways of establishing alpha-equivalence        *)
(* 1. Given a variable x:v, we always have x ~ x.               *)
(* 2. t1 ~ t1' and t2 ~ t2' implies t1 t2 ~ t1' t2'             *)
(* 3. t1 ~ t1' implies Lam x t1 ~ Lam x t1'                     *)
(* 4. The final and most interesting way relies on swap         *)
(* In order to establish the equivalence Lam x t1 ~ Lam y t1'   *)
(* in the case when x <> y, we need to ensure that y is not     *)
(* a free variable of t1, and furthermore that t1' ~ t1[x:y]    *)
(* i.e. that t1' is equivalent to t1 after x and y have been    *)
(* exchanged for one another. Note that we cannot do away with  *)
(* the third constructor (by removing condition x <> y in 4.)   *)
(* Lam x (Var x) ~ Lam x (Var x) cannot be proven simply by     *)
(* taking x = y in a variant of 4. because of the requirement   *)
(* that y be not a free variable of t1.                         *)

Inductive alpha (v:Type) (p:Eq v) : P v -> P v -> Prop :=
| AVar  : forall (x:v), alpha v p (Var x) (Var x)
| AApp  : forall (t1 t1' t2 t2':P v), 
    alpha v p t1 t1' -> alpha v p t2 t2' -> alpha v p (App t1 t2) (App t1' t2')
| ALam1 :forall (x:v) (t1 t1':P v), 
    alpha v p t1 t1' -> alpha v p (Lam x t1) (Lam x t1') 
| ALam2 : forall (x y:v) (t1 t1':P v),
    x <> y -> ~In y (Fr p t1) -> alpha v p t1' (swap p x y t1) ->
    alpha v p (Lam x t1) (Lam y t1')
.

Arguments alpha {v} _ _ _.

(* alpha-equivalent terms have the same free variables *)
(* In fact, this equality holds as lists, not just as set *)
Lemma alpha_free : forall (v:Type) (p:Eq v) (t t':P v),
    alpha p t t' -> Fr p t = Fr p t'.
Proof.
    intros v p t t' H.
    induction H.
    - reflexivity.
    - simpl.
        assert (Fr p t1 = Fr p t1') as E1. { assumption. }
        assert (Fr p t2 = Fr p t2') as E2. { assumption. }
        rewrite E1, E2. reflexivity.
    - simpl.
        assert (Fr p t1 = Fr p t1') as E1. { assumption. }
        rewrite E1. reflexivity.
    - simpl. assert (Fr p t1' = Fr p (swap p x y t1)) as E. { assumption. }
      rewrite E. unfold swap. rewrite (free_vmap_inj v v p p).
      remember (permute p x y) as f eqn:F.
      assert (f x = y) as Fx. { rewrite F. apply permute_x. }
      rewrite <- Fx. rewrite (remove_inj2 v v p p).
        + symmetry. apply map_invariant. 
            { intros u Hu. rewrite F. apply permute_not_xy.
                { intros H'. rewrite H' in Hu. revert Hu. apply remove_In. }
                { intros H'. rewrite H' in Hu. apply H0.
                    apply (remove_incl v p x). assumption.
                }
            }
        + apply inj_is_inj_on_list. rewrite F. apply permute_injective.
        + apply inj_is_inj_on_list. apply permute_injective.
Qed.

(* two alpha-equivalent terms are still alpha-equivalent after      *)
(* injective variable renaming                                      *)
Lemma alpha_injective : forall (v w:Type) (p:Eq v) (q:Eq w) (t t':P v) (f:v -> w),
    injective f -> alpha p t t' -> alpha q (vmap f t) (vmap f t').
Proof.
    intros v w p q t t' f I H. induction H; simpl.
    - constructor.
    - constructor; assumption.
    - constructor; assumption.
    - constructor.
        + intros H'. apply H. apply I. assumption.
        + rewrite (free_vmap_inj v w p q).
            { apply injective_not_in.
                { apply inj_is_inj_on_list. assumption. }
                { assumption. }
            }
            { apply inj_is_inj_on_list. assumption. }
        + rewrite <- (swap_inj v w p q); assumption.
Qed.


(* alpha-equivalence is a reflexive relation *)
Lemma alpha_refl : forall (v:Type) (p:Eq v) (t:P v), alpha p t t.
Proof.
    intros v p t.
    induction t.
    - constructor.
    - constructor; assumption.
    - constructor; assumption.
Qed.


(* alpha-equivalence is a symmetric relation *)
Lemma alpha_sym : forall (v:Type) (p:Eq v) (t t':P v), 
    alpha p t t' -> alpha p t' t.
Proof.
    intros v p t t' H. 
    induction H.
    - constructor.
    - constructor; assumption.
    - constructor; assumption.
    - constructor.
        + intros E. apply H. symmetry. assumption.
        + assert (Fr p t1' = Fr p (swap p x y t1)) as H'.
            { apply alpha_free. assumption. }
          rewrite H'. clear H'. unfold swap.
          remember (permute p x y) as f eqn:F.
          assert (Fr p (vmap f t1) = map f (Fr p t1)) as H'.
            { apply free_vmap_inj. apply inj_is_inj_on_list. 
              rewrite F. apply permute_injective.
            }
          rewrite H'. clear H'.
          assert (f y = x) as H'.
            { rewrite F. apply permute_y. }
          rewrite <- H'. clear H'.
          apply injective_not_in.
            { apply inj_is_inj_on_list. rewrite F. apply permute_injective. }
            { assumption. }
        + rewrite swap_commute. rewrite <- (swap_involution v p x y t1).
          apply (alpha_injective v v p p).
            { apply permute_injective. }
            { assumption. }
Qed.

(* Technical lemma: this is motivated and constitues a generalization of    *)
(* t ~ t'[x:y]  <=>   t[x:y] ~ t'                                           *)
(* We are now stating that:                                                 *)
(* t ~ f t'     <=>   g t ~  t'                                             *)
(* provided f and g are inverses of each other.                             *) 
Lemma alpha_swap_gen : forall (v:Type) (p:Eq v) (t t':P v) (f g:v -> v),
    (forall x, g (f x) = x) -> 
    (forall x, f (g x) = x) ->
    alpha p t (vmap f t') <-> alpha p (vmap g t) t'.
Proof.
    intros v p t t' f g GF FG. split; intros H'.
    - rewrite <- (vmap_id v t'). rewrite (vmap_eq v v id (g;f) t').
        + rewrite vmap_comp. apply alpha_injective with p.
            { intros x y Hxy. rewrite <- (FG x), <- (FG y), Hxy. reflexivity. }
            { assumption. }
        + intros x _. symmetry. apply GF.
    - rewrite <- (vmap_id v t). rewrite (vmap_eq v v id (f;g) t).
        + rewrite vmap_comp. apply alpha_injective with p.
            { intros x y Hxy. rewrite <- (GF x), <- (GF y), Hxy. reflexivity. }
            { assumption. }
        + intros x _. symmetry. apply FG.
Qed.

(* Technical lemma: apply alpha_swap_gen to (permute p x y) *)
Lemma alpha_swap : forall (v:Type) (p:Eq v) (x y:v) (t t':P v),
    alpha p t (swap p x y t') <-> alpha p (swap p x y t) t'.
Proof.
    intros v p x y t t'. unfold swap. apply alpha_swap_gen;
    intros z; apply permute_involution.
Qed.

(* Technical lemma: simple convenience wrapper *)
Lemma alpha_swap_gen' : forall (v:Type) (p:Eq v) (t t' s:P v) (f g:v -> v),
    adpair p s f g -> 
    alpha p t (vmap f t') <-> alpha p (vmap g t) t'.
Proof. intros v p t t' s f g [GF FG _]. apply alpha_swap_gen; assumption. Qed.


(* Technical lemma: if t[x:y] ~ t' then x is not a free variable of t'  *)
(* if and only if y is not a free variable of t.                        *)
Lemma alpha_free_swap : forall (v:Type) (p:Eq v) (x y:v) (t t':P v),
    alpha p (swap p x y t) t' -> ( ~In y (Fr p t) <-> ~In x (Fr p t')). 
Proof.
    intros v p x y t t' H. split; intros H'.
    - rewrite (alpha_free v p t' (swap p x y t)).
        + apply free_swap. assumption.
        + apply alpha_sym. assumption.
    - apply alpha_swap in H. rewrite (alpha_free v p t (swap p x y t')).
        + rewrite swap_commute. apply free_swap. assumption.
        + assumption.
Qed.

(*
Lemma alpha_adpair : forall (v:Type) (p:Eq v) (f g:v -> v) (t s:P v),
    adpair p t f g -> alpha p s t -> alpha p s (vmap f t).
Proof.
    intros v p f g t s A H. revert f g A.
    induction H; intros f g A; simpl.
    - rewrite (adpair_invl v p (Var x) f g).
        + constructor.
        + assumption.
        + simpl. left. reflexivity.
    - constructor.
        + apply IHalpha1 with g. apply adpair_Appl with t2'. assumption.
        + apply IHalpha2 with g. apply adpair_Appr with t1'. assumption.
    - remember (f x) as y eqn:Y. destruct (p y x) as [Hyx|Hyx].
        + rewrite Hyx. constructor. apply IHalpha with g. constructor.
            { intros z. apply (adpair_gf v p) with (Lam x t1'). assumption. }
            { intros z. apply (adpair_fg v p) with (Lam x t1'). assumption. }
            { intros z Hz. destruct (p x z) as [Hxz|Hxz]; subst.
                { assumption. }
                { apply (adpair_invl v p (Lam x t1')) with g.
                    { assumption. }
                    { simpl. apply remove_In2; assumption. }
                }
            }
        + constructor.
            { apply neq_sym. assumption. }
            { intros H'. apply Hyx. assert (injective f) as I. 
                { apply (adpair_injl v p (Lam x t1')) with g. assumption. }
              apply I. rewrite <- Y.
              apply (adpair_invl v p (Lam x t1')) with g.
                { assumption. }
                { simpl. apply remove_In2.
                    { apply neq_sym. assumption. }
                    { rewrite (alpha_free v p t1' t1).
                        { assumption. }
                        { apply alpha_sym. assumption. }
                    }
                }
            }
            { apply alpha_sym. apply alpha_swap. unfold swap.
              rewrite <- vmap_comp. apply IHalpha with (g; permute p x y).
              constructor.
                { intros z. unfold comp. rewrite permute_involution.
                  apply (adpair_gf v p (Lam x t1')). assumption.
                }
                { intros z. unfold comp.
                    rewrite (adpair_fg v p (Lam x t1') f g (permute p x y z)).
                        { apply permute_involution. }
                        { assumption. }
                }
                { intros z Hz. destruct (p z x) as [Hzx|Hzx]; unfold comp.
                    { rewrite Hzx. rewrite <- Y. apply permute_y. }
                    { assert (f z = z) as Z.
                        { apply (adpair_invl v p (Lam x t1')) with g.
                            { assumption. }
                            { simpl. apply remove_In2.
                                { apply neq_sym. assumption. }
                                { assumption. }
                            }
                        }
                      rewrite Z. apply permute_not_xy.
                        { assumption. }
                        { intros H'. apply Hzx. assert (injective f) as I.
                            { apply (adpair_injl v p (Lam x t1')) with g. 
                              assumption. 
                            }
                          apply I. rewrite <- Y. rewrite <- H'.
                          apply (adpair_invl v p (Lam x t1')) with g.
                            { assumption. }
                            { simpl. apply remove_In2.
                                { apply neq_sym. assumption. }
                                { assumption. }
                            }
                        }
                    }
                }
            }
    - remember (f y) as z eqn:Z. destruct (p x z) as [Hxz|Hxz].
        + rewrite <- Hxz. constructor. 
          rewrite (alpha_swap_gen' v p t1 t1' (Lam y t1') f g).
            { apply alpha_sym.
              rewrite <- (swap_involution v p x y t1).
              unfold swap at 1.
              rewrite <- vmap_comp.
              apply IHalpha with (permute p x y ; f).
              constructor; generalize A; intros [GF FG _].
                { intros u. unfold comp. rewrite FG. apply permute_involution. }
                { intros u. unfold comp. rewrite permute_involution. apply GF. }
                { intros u Hu. unfold comp. destruct (p u y) as [Huy|Huy].
                    { rewrite Huy, permute_y, Hxz, Z. apply GF. }
                    { apply adpair_sym in A. generalize A. intros [_ _ FR].
                      rewrite permute_not_xy.
                        { apply FR. simpl. apply remove_In2.
                            { apply neq_sym. assumption. }
                            { rewrite (alpha_free v p t1' (swap p x y t1));
                              assumption.
                            }
                        }
                        { intros Hux. rewrite (free_swap v p x y t1) in H0.
                          apply H0. rewrite <- Hux at 1. assumption.
                        }
                        { assumption. }
                    }
                }
            }
            { assumption. }
        + constructor.
            { assumption. }
            { intros H'. apply adpair_sym in A. 
              generalize A. intros [FG GF FR]. assert (y = z) as Hyz.
                { rewrite <- (GF y), <- Z. apply FR. simpl.
                  apply remove_In2.
                    { intros Hyz. apply H0. rewrite Hyz. assumption. }
                    { rewrite (alpha_free v p t1' (swap p x y t1)).
                        { rewrite free_permute, <- (permute_not_xy v p x y z).
                            { apply incl_map. assumption. }
                            { apply neq_sym. assumption. }
                            { intros Hyz. apply H0. rewrite <- Hyz. assumption. } 
                        }
                        { assumption. }
                    } 
                }
              apply H0. rewrite Hyz. assumption. 
            }
            { apply alpha_sym. 
              apply (alpha_swap_gen v p (swap p x z t1) t1' f g);
              generalize A; intros [GF FG _]. 
                { apply GF. }
                { apply FG. }
                { apply alpha_sym. rewrite <- (swap_involution v p x y t1). 
                  unfold swap at 1. rewrite <- vmap_comp. 
                  unfold swap at 1. rewrite <- vmap_comp.
                  apply IHalpha with ((permute p x y); (permute p x z; f)).
                  constructor.
                  { intros u. unfold comp. rewrite FG. 
                    rewrite permute_involution, permute_involution.
                    reflexivity.
                  }
                  { intros u. unfold comp.
                    rewrite permute_involution, permute_involution, GF.
                    reflexivity.
                  }
                  { intros u Hu. unfold comp.
 
Show.
*)

(*
Lemma alpha_permute_not_free : forall (v:Type) (p:Eq v) (x y:v) (t s:P v),
    ~In x (Fr p t) -> ~In y (Fr p t) -> alpha p s t -> alpha p s (swap p x y t).
Proof.
    intros v p x y t s Hx Hy H. revert x y Hx Hy.
    induction H; simpl; intros x' y' Hx Hy.
    - unfold swap. simpl. rewrite permute_not_xy. 
        + constructor.
        + intros Gx. apply Hx. left. assumption.
        + intros Gy. apply Hy. left. assumption.
    - unfold swap. simpl. constructor.   
        + apply IHalpha1.
            { intros Gx. apply Hx. apply in_or_app. left. assumption. }
            { intros Gy. apply Hy. apply in_or_app. left. assumption. }
        + apply IHalpha2. 
            { intros Gx. apply Hx. apply in_or_app. right. assumption. }
            { intros Gy. apply Hy. apply in_or_app. right. assumption. }
    - unfold swap. simpl.

Show.
*)


(*
Lemma alpha_tran_ : forall (v:Type) (p:Eq v) (t t': P v),
    alpha p t t' -> (forall (s:P v), alpha p t s <-> alpha p t' s).
Proof.
    intros v p t t' H.
    induction H; intros s.
    - split; intros H'; assumption.
    - split; intros H'; inversion H'; constructor; subst.
        + apply IHalpha1. assumption.
        + apply IHalpha2. assumption.
        + apply IHalpha1. assumption.
        + apply IHalpha2. assumption.
    - split; intros H'; inversion H'; constructor; subst.
        + apply IHalpha. assumption.
        + assumption.
        + assert (Fr p t1' = Fr p t1) as F.
            { apply alpha_free. apply IHalpha. apply alpha_refl. }
          rewrite F. assumption.
        + apply alpha_swap. apply alpha_sym. apply IHalpha.  
          apply alpha_sym. apply alpha_swap. assumption.
        + apply IHalpha. assumption.
        + assumption.
        + assert (Fr p t1 = Fr p t1') as F.
            { apply alpha_free. apply IHalpha. apply alpha_refl. }
          rewrite F. assumption.
        + apply alpha_swap. apply alpha_sym. apply IHalpha.  
          apply alpha_sym. apply alpha_swap. assumption.
       - split; intros H'; inversion H'; subst.
            + constructor.
                { intros E. apply H. symmetry. assumption. }
                { apply (alpha_not_free_swap v p x y t1 t1').
                    { apply IHalpha. apply alpha_refl. }
                    { assumption. }
                }
                { apply alpha_swap. apply alpha_sym. apply IHalpha.
                  rewrite (swap_commute v p y x). 
                  apply (alpha_injective v v p p).
                    { apply permute_injective. }
                    { assumption. }
                }
            + destruct (p y y0) as [Hy0|Hy0]; subst.
                { constructor. apply IHalpha. apply alpha_sym. assumption. }
                { constructor.
                    { assumption. }
                    { rewrite (alpha_free v p t1' (swap p x y t1)). 
                        { rewrite free_permute.
                          rewrite <- (permute_not_xy v p x y y0).
                            { apply injective_not_in.
                                { apply inj_is_inj_on_list.
                                  apply permute_injective.
                                }
                                { assumption. }
                            }
                            { intros E. apply H4. symmetry. assumption. }
                            { intros E. apply Hy0. symmetry. assumption. }
                        }
                        { assumption. }
                    }
                    { rename y0 into z. rename t1'0 into t0. rename t1' into t2. 
Show.
*)


(*
Lemma alpha_tran : forall (v:Type) (p:Eq v) (t1 t2 t3:P v),
    alpha p t1 t2 -> alpha p t2 t3 -> alpha p t1 t3.
Proof.
    intros v p t1 t2 t3 H12. revert t3.
*)
(*
    induction H12; intros t3 H23.
    - assumption.
    - inversion H23. subst. constructor.
        + apply IHalpha1. assumption.
        + apply IHalpha2. assumption.
    - inversion H23; subst.
        + constructor. apply IHalpha. assumption.
        + constructor.
            { assumption. }
            { assert (Fr p t1 = Fr p t1') as F. 
                { apply alpha_free. apply IHalpha. apply alpha_refl. }
                { rewrite F. assumption. }
            }
            { rewrite <- (swap_involution v p x y t1'0).
              apply (alpha_injective v v p p).
                { apply permute_injective. }
                { apply alpha_sym. apply IHalpha.
                  rewrite <- (swap_involution v p x y t1').
                  apply (alpha_injective v v p p).
                    { apply permute_injective. }
                    { apply alpha_sym. assumption. }
                }
            }
    - 
*)
(*        
        
      remember (Lam y t1') as t3' eqn:T3. 
      revert T3.
      revert IHalpha.
      revert H12.
      revert H0.
      revert H.
      revert t1.
      revert t1'.
      induction H23; intros s0 s1 Exy Hy A0 IH H'; inversion H'; subst.
        + constructor.
            { assumption. }
            { assumption. }
            {
*)      




