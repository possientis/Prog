Require Import List.
Import ListNotations.

Require Import Eq.
Require Import Map.
Require Import Remove.
Require Import Replace.
Require Import Include.
Require Import Coincide.
Require Import Relation.
Require Import Injective.

Require Import Fol.P.
Require Import Fol.Variable.
Require Import Fol.Congruence.

(* Returns the list of free variables (with possible duplication) in a term     *)
(* When facing a forall quantification, we need to be able to remove a variable *)
(* from the list of free variables of the subterm, hence decidable equality.    *)
Fixpoint free (v:Type) (e:Eq v) (p:P v) : list v :=
    match p with
    | Bot           => [ ]
    | Elem x y      => [x;y]
    | Imp p1 p2     => free v e p1 ++ free v e p2
    | All x p1      => remove e x (free v e p1)
    end.

Arguments free {v} _ _.


(* The free variables of the proposition (fmap f p) are a subset of the images  *)
(* by f of the free variables of the proposition p.                             *)
Lemma free_fmap : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (p:P v),
    incl (free e' (fmap f p)) (map f (free e p)).
Proof.
    intros v w e e' f.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - apply incl_refl.
    - apply incl_refl.
    - rewrite map_app. apply incl_app.
        + apply incl_appl, IH1.
        + apply incl_appr, IH2.
    - apply incl_tran with (remove e' (f x) (map f (free e p1))). 
        + apply remove_mon, IH1.
        + apply incl_tran with (map f (remove e x (free e p1))).
            { apply remove_map. }
            { apply incl_refl. }
Qed.

(* A free variable is a variable                                                *)
Lemma free_var : forall (v:Type) (e:Eq v) (p:P v), 
    incl (free e p) (var p).
Proof.
    intros v e.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - apply incl_refl.
    - apply incl_refl.
    - apply incl_app2; assumption.
    - apply incl_tran with (free e p1).
        + apply remove_incl.
        + apply incl_tl. assumption.
Qed.


Lemma free_inj : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (p:P v),
    injective_on (var p) f -> free e' (fmap f p) = map f (free e p).
Proof.
    intros v w e e' f.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl; intros H.
    - reflexivity.
    - reflexivity.
    - rewrite map_app, IH1, IH2.
        + reflexivity.
        + apply injective_on_appr with (var p1). assumption.
        + apply injective_on_appl with (var p2). assumption.
    - rewrite IH1. apply remove_inj2. apply injective_on_incl with (x :: var p1).
        + apply incl_cons.
            { left. reflexivity. }
            { apply incl_tl, free_var. }
        + assumption.
        + apply injective_on_cons with x. assumption.
Qed.

Lemma free_replace1 : forall (v:Type) (e:Eq v) (p:P v) (x y:v), 
    ~In y (var p)    -> 
    ~In x (free e p) -> 
    free e (fmap (replace e x y) p) = free e p.
Proof.
    intros v e p x y Hy Hx. 
    rewrite (free_inj v v e e).
    - rewrite <- map_id. apply coincide_map. unfold coincide.
      intros u H. rewrite replace_not_x.
        + reflexivity.
        + intros E. subst. apply Hx, H.
    - apply replace_inj. assumption.
Qed.

Lemma free_replace2 : forall (v:Type) (e:Eq v) (p:P v) (x y:v),
    ~In y (var p)    ->
     In x (free e p) -> 
     forall (z:v), 
        In z (free e (fmap (replace e x y) p)) <-> 
        (z = y) \/ (In z (free e p) /\ (z <> x)). 
Proof.
    intros v e p x y Hy Hx z. rewrite (free_inj v v e e). split.
    - intros H. destruct (e z y) as [Hzy|Hzy]. 
        + left. assumption.
        + right. apply mapIn in H. destruct H as [u [H1 H2]]. split.
            { destruct (e u x) as [Hux|Hux].
                { rewrite Hux, replace_x in H2. exfalso.
                  apply Hzy. assumption.
                }
                { rewrite replace_not_x in H2.
                    { rewrite H2. assumption. }
                    { assumption. }
                }
            }
            { intros Hzx. rewrite Hzx in H2.
              destruct (e u x) as [Hux|Hux].
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
    congruence (fun (p q:P v) => free e p = free e q).
Proof.
    intros v e. split.
    - split.
        + intros p. reflexivity.
        + split.
            { intros p q H. symmetry. assumption. }
            { intros p q r Hpq Hqr. 
              apply eq_trans with (free e q); assumption. }
    - split.
        + intros p1 p2 q1 q2 H1 H2. simpl. rewrite H1, H2. reflexivity.
        + intros x p1 q1 H1. simpl. rewrite H1. reflexivity.
Qed.


