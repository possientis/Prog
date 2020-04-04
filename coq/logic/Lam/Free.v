Require Import List.

Require Import In.
Require Import Eq.
Require Import Map.
Require Import Remove.
Require Import Replace.
Require Import Include.
Require Import Coincide.
Require Import Relation.
Require Import Injective.
Require Import Intersect.
Require Import Difference.
Require Import Composition.

Require Import Lam.T.
Require Import Lam.Subst.
Require Import Lam.Variable.
Require Import Lam.Congruence.

(* Returns the list of free variables (with possible duplication) in a term     *)
(* When facing a lambda abstraction, we need to be able to remove a variable    *)
(* from the list of free variables of the subterm, hence decidable equality.    *)
Fixpoint free (v:Type) (e:Eq v) (t:T v) : list v :=
    match t with
    | Var x         => (cons x nil)
    | App t1 t2     => free v e t1 ++ free v e t2
    | Lam x t1      => remove x (free v e t1)
    end.

Arguments free {v} {e} _.

(* The free variables of the term (fmap f t) are a subset of the images by f    *)
(* of the free variables of the term t.                                         *)
Lemma free_fmap : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    free (fmap f t) <= map f (free t).
Proof.
    intros v w e e' f.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - apply incl_refl.
    - rewrite map_app. apply incl_app.
        + apply incl_appl, IH1.
        + apply incl_appr, IH2.
    - apply incl_tran with (remove (f x) (map f (free t1))). 
        + apply remove_mon, IH1.
        + apply incl_tran with (map f (remove x (free t1))).
            { apply remove_map_incl. }
            { apply incl_refl. }
Qed.

(* A free variable is a variable                                                *)
Lemma free_var : forall (v:Type) (e:Eq v) (t:T v), free t <= var t.
Proof.
    intros v e.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - apply incl_refl.
    - apply incl_app2; assumption.
    - apply incl_tran with (free t1).
        + apply remove_incl.
        + apply incl_tl. assumption.
Qed.

Lemma free_inj : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    injective_on (var t) f -> free (fmap f t) = map f (free t).
Proof.
    intros v w e e' f.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl; intros H.
    - reflexivity.
    - rewrite map_app, IH1, IH2.
        + reflexivity.
        + apply injective_on_appr with (var t1). assumption.
        + apply injective_on_appl with (var t2). assumption.
    - rewrite IH1. apply remove_inj2. 
      apply injective_on_incl with (cons x (var t1)).
        + apply incl_cons.
            { left. reflexivity. }
            { apply incl_tl, free_var. }
        + assumption.
        + apply injective_on_cons with x. assumption.
Qed.


Lemma free_replace1 : forall (v:Type) (e:Eq v) (t:T v) (x y:v), 
    ~ y :: var t    -> 
    ~ x :: free t   -> 
    free (fmap (y // x) t) = free t.
Proof.
    intros v e t x y Hy Hx. 
    rewrite (free_inj v v e e).
    - rewrite <- map_id. apply coincide_map. unfold coincide.
      intros u H. rewrite replace_not_x.
        + reflexivity.
        + intros E. subst. apply Hx, H.
    - apply replace_inj. assumption.
Qed.

(* We lack set theoretic notations to express this result nicely                *)
Lemma free_replace2 : forall (v:Type) (e:Eq v) (t:T v) (x y:v),
    ~ y :: var t  ->
      x :: free t -> 
     forall (z:v), 
        z :: free (fmap (y // x) t) <-> 
        z = y \/ (z :: free t) /\ z <> x. 
Proof.
    intros v e t x y Hy Hx z. rewrite (free_inj v v e e). split.
    - intros H. destruct (eqDec z y) as [Hzy|Hzy]. 
        + left. assumption.
        + right. apply mapIn in H. destruct H as [u [H1 H2]]. split.
            { destruct (eqDec u x) as [Hux|Hux].
                { rewrite Hux, replace_x in H2. exfalso.
                  apply Hzy. assumption.
                }
                { rewrite replace_not_x in H2.
                    { rewrite H2. assumption. }
                    { assumption. }
                }
            }
            { intros Hzx. rewrite Hzx in H2.
              destruct (eqDec u x) as [Hux|Hux].
                { rewrite Hux, replace_x, <- Hzx in H2.
                  apply Hzy. assumption.
                }
                { rewrite replace_not_x in H2.
                    { apply Hux. symmetry. assumption. }
                    { assumption. }
                }
            }
    - intros [H|[H1 H2]]; apply mapIn.
        + exists x. split.
            { assumption. }
            { rewrite replace_x. assumption. }
        + exists z. split.
            { assumption. }
            { rewrite replace_not_x.
                { reflexivity. }
                { assumption. }
            }
    - apply replace_inj. assumption.
Qed.

Lemma free_congruence : forall (v:Type) (e:Eq v), 
    congruence (fun (s t:T v) => free s = free t).
Proof.
    intros v e. split.
    - split.
        + intros t. reflexivity.
        + split.
            { intros s t H. symmetry. assumption. }
            { intros r s t Hrs Hst. 
              apply eq_trans with (free s); assumption. }
    - split.
        + intros s1 s2 t1 t2 H1 H2. simpl. rewrite H1, H2. reflexivity.
        + intros x s1 t1 H1. simpl. rewrite H1. reflexivity.
Qed.

(*
Lemma free_fmap_gen : forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v) (xs:list v),
    free (subst_ f xs t) <= (free t /\ xs) ++ concat (map (free ; f) (free t \\ xs)).
Proof.

Show.
*)
