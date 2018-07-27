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

(*
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
        +

Show.
*)

(*
Lemma alpha_refl: forall (v:Type) (p:Eq v) (t:P v), alpha p t t.
Proof.
    intros v p t.
    induction t.
    - constructor.
    - constructor; assumption.
    - constructor; assumption.
Qed.
*)

(*
Lemma alpha_sym: forall (v:Type) (p:Eq v) (t t':P v), 
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
        +
Show.
*)


