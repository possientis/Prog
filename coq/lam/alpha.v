Require Import List.
Import ListNotations.

Require Import eq.
Require Import injective.
Require Import map.
Require Import term.
Require Import inj_on_list.
Require Import permute.
Require Import inj_on_term.
Require Import remove.
Require Import free.
Require Import vmap.
Require Import swap.



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



Lemma alpha_refl : forall (v:Type) (p:Eq v) (t:P v), alpha p t t.
Proof.
    intros v p t.
    induction t.
    - constructor.
    - constructor; assumption.
    - constructor; assumption.
Qed.



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


Lemma alpha_swap : forall (v:Type) (p:Eq v) (x y:v) (t t':P v),
    alpha p t (swap p x y t') <-> alpha p (swap p x y t) t'.
Proof.
    intros v p x y t t'. split; intros H.
    - rewrite <- (swap_involution v p x y t').
      apply (alpha_injective v v p p).
      + apply permute_injective.
      + assumption. 
    - rewrite <- (swap_involution v p x y t).
      apply (alpha_injective v v p p).
      + apply permute_injective.
      + assumption. 
Qed.

Lemma alpha_not_free_swap : forall (v:Type) (p:Eq v) (x y:v) (t t':P v),
    alpha p (swap p x y t) t' -> ( ~In y (Fr p t) <-> ~In x (Fr p t')). 
Proof.
    intros v p x y t t' H. split; intros H'.
    - rewrite (alpha_free v p t' (swap p x y t)).
        + unfold swap. rewrite (free_vmap_inj v v p p).
            { remember (permute p x y) as f eqn:F. 
              assert (x = f y) as X.
                { symmetry. rewrite F. apply permute_y. }
              rewrite X. apply injective_not_in.
                  { apply inj_is_inj_on_list.
                    rewrite F. apply permute_injective.
                  }
                  { assumption. }
            }
            { apply inj_is_inj_on_list. apply permute_injective. }
        + apply alpha_sym. assumption.
    - apply alpha_swap in H.
      rewrite (alpha_free v p t (swap p x y t')).
        + unfold swap. rewrite (free_vmap_inj v v p p).
            { remember (permute p x y) as f eqn:F. 
              assert (y = f x) as Y.
                { symmetry. rewrite F. apply permute_x. }
              
              rewrite Y. apply injective_not_in.
                  { apply inj_is_inj_on_list.
                    rewrite F. apply permute_injective.
                  }
                  { assumption. }
            }
            { apply inj_is_inj_on_list. apply permute_injective. }
        + assumption.
Qed.

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
                    { apply alpha_swap. apply alpha_sym.
                      apply IHalpha. apply alpha_swap.
                      apply alpha_sym.
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




