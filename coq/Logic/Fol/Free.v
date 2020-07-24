Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Rel.Properties.

Require Import Logic.Func.Replace.

Require Import Logic.List.In.
Require Import Logic.List.Remove.
Require Import Logic.List.Replace.
Require Import Logic.List.Include.
Require Import Logic.List.Coincide.
Require Import Logic.List.InjectiveOn.

Require Import Logic.Fol.Syntax.
Require Import Logic.Fol.Functor.
Require Import Logic.Fol.Variable.
Require Import Logic.Fol.Congruence.

(* Returns the list of free variables (with possible duplication) in a term     *)
(* When facing a forall quantification, we need to be able to remove a variable *)
(* from the list of free variables of the subterm, hence decidable equality.    *)
Fixpoint Fr (v:Type) (e:Eq v) (p:P v) : list v :=
    match p with
    | Bot           => nil
    | Elem x y      => cons x (cons y nil)
    | Imp p1 p2     => Fr v e p1 ++ Fr v e p2
    | All x p1      => remove x (Fr v e p1)
    end.

Arguments Fr {v} {e} _.


(* The free variables of the proposition (fmap f p) are a subset of the images  *)
(* by f of the free variables of the proposition p.                             *)
Lemma free_fmap : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (p:P v),
    Fr (fmap f p) <= map f (Fr p).
Proof.
    intros v w e e' f.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - apply incl_refl.
    - apply incl_refl.
    - rewrite map_app. apply incl_app.
        + apply incl_appl, IH1.
        + apply incl_appr, IH2.
    - apply incl_tran with (remove (f x) (map f (Fr p1))). 
        + apply remove_mon, IH1.
        + apply incl_tran with (map f (remove x (Fr p1))).
            { apply remove_map_incl. }
            { apply incl_refl. }
Qed.

(* A free variable is a variable                                                *)
Lemma free_var : forall (v:Type) (e:Eq v) (p:P v), Fr p <= var p.
Proof.
    intros v e.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - apply incl_refl.
    - apply incl_refl.
    - apply incl_app2; assumption.
    - apply incl_tran with (Fr p1).
        + apply remove_incl.
        + apply incl_tl. assumption.
Qed.


Lemma free_inj : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (p:P v),
    injective_on (var p) f -> Fr (fmap f p) = map f (Fr p).
Proof.
    intros v w e e' f.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl; intros H.
    - reflexivity.
    - reflexivity.
    - rewrite map_app, IH1, IH2.
        + reflexivity.
        + apply injective_on_appr with (var p1). assumption.
        + apply injective_on_appl with (var p2). assumption.
    - rewrite IH1. apply remove_inj2. apply injective_on_incl with (cons x (var p1)).
        + apply incl_cons.
            { left. reflexivity. }
            { apply incl_tl, free_var. }
        + assumption.
        + apply injective_on_cons with x. assumption.
Qed.

Lemma free_replace1 : forall (v:Type) (e:Eq v) (p:P v) (x y:v), 
    ~ y :: (var p)  -> 
    ~ x :: (Fr p) -> 
    Fr (fmap (y // x) p) = Fr p.
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
    ~ y :: (var p)  ->
      x :: (Fr p) -> 
     forall (z:v), 
        z :: Fr (fmap (y // x) p) <-> 
        z = y \/ (z :: Fr p) /\ z <> x. 
Proof.
    intros v e p x y Hy Hx z. rewrite (free_inj v v e e). split.
    - intros H. destruct (eqDec z y) as [Hzy|Hzy]. 
        + left. assumption.
        + right. apply in_map_iff in H. destruct H as [u [H1 H2]]. split.
            { destruct (eqDec u x) as [Hux|Hux].
                { rewrite Hux, replace_x in H1. exfalso.
                  apply Hzy. symmetry. assumption. }
                { rewrite replace_not_x in H1.
                    { rewrite <- H1. assumption. }
                    { assumption. }}}
            { intros Hzx. rewrite Hzx in H1.
              destruct (eqDec u x) as [Hux|Hux].
                { rewrite Hux, replace_x, <- Hzx in H1.
                  apply Hzy. symmetry. assumption. }
                { rewrite replace_not_x in H1.
                    { apply Hux. assumption. }
                    { assumption. }}}
   - intros [H|[H1 H2]]; apply in_map_iff.
        + exists x. split.
            { rewrite replace_x. symmetry. assumption. }
            { assumption. }
        + exists z. split.
            { rewrite replace_not_x.
                { reflexivity. }
                { assumption. }}
            { assumption. }
    - apply replace_inj. assumption.
Qed.

Lemma free_congruence : forall (v:Type) (e:Eq v), 
    congruence (fun (p q:P v) => Fr p = Fr q).
Proof.
    intros v e. split.
    - split.
        + intros p. reflexivity.
        + split.
            { intros p q H. symmetry. assumption. }
            { intros p q r Hpq Hqr. 
              apply eq_trans with (Fr q); assumption. }
    - split.
        + intros p1 p2 q1 q2 H1 H2. simpl. rewrite H1, H2. reflexivity.
        + intros x p1 q1 H1. simpl. rewrite H1. reflexivity.
Qed.

