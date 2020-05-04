Require Import List.

Require Import In.
Require Import Eq.
Require Import Equiv.
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
Fixpoint Fr (v:Type) (e:Eq v) (t:T v) : list v :=
    match t with
    | Var x         => (cons x nil)
    | App t1 t2     => Fr v e t1 ++ Fr v e t2
    | Lam x t1      => remove x (Fr v e t1)
    end.

Arguments Fr {v} {e} _.

(* The free variables of the term (fmap f t) are a subset of the images by f    *)
(* of the free variables of the term t.                                         *)
Lemma free_fmap : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    Fr (fmap f t) <= map f (Fr t).
Proof.
    intros v w e e' f.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - apply incl_refl.
    - rewrite map_app. apply incl_app.
        + apply incl_appl, IH1.
        + apply incl_appr, IH2.
    - apply incl_tran with (remove (f x) (map f (Fr t1))). 
        + apply remove_mon, IH1.
        + apply incl_tran with (map f (remove x (Fr t1))).
            { apply remove_map_incl. }
            { apply incl_refl. }
Qed.

(* A free variable is a variable                                                *)
Lemma free_var : forall (v:Type) (e:Eq v) (t:T v), Fr t <= var t.
Proof.
    intros v e.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - apply incl_refl.
    - apply incl_app2; assumption.
    - apply incl_tran with (Fr t1).
        + apply remove_incl.
        + apply incl_tl. assumption.
Qed.

Lemma free_inj : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    injective_on (var t) f -> Fr (fmap f t) = map f (Fr t).
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
    ~ x :: Fr t   -> 
    Fr (fmap (y // x) t) = Fr t.
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
      x :: Fr t -> 
     forall (z:v), 
        z :: Fr (fmap (y // x) t) <-> 
        z = y \/ (z :: Fr t) /\ z <> x. 
Proof.
    intros v e t x y Hy Hx z. rewrite (free_inj v v e e). split.
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
    congruence (fun (s t:T v) => Fr s = Fr t).
Proof.
    intros v e. split.
    - split.
        + intros t. reflexivity.
        + split.
            { intros s t H. symmetry. assumption. }
            { intros r s t Hrs Hst. 
              apply eq_trans with (Fr s); assumption. }
    - split.
        + intros s1 s2 t1 t2 H1 H2. simpl. rewrite H1, H2. reflexivity.
        + intros x s1 t1 H1. simpl. rewrite H1. reflexivity.
Qed.


Lemma free_subst_gen : forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v) (xs:list v),
    Fr (subst_ f xs t) <= (Fr t /\ xs) ++ concat (map (Fr ; f) (Fr t \\ xs)).
Proof.
    intros v e f. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs; simpl.
    - destruct (in_dec eqDec x xs) as [H|H]; simpl.
        + apply incl_refl.
        + unfold comp. rewrite app_nil_r. apply incl_refl.
    - apply incl_app. 
        + apply incl_tran with 
            ((Fr t1 /\ xs) ++ concat (map (Fr; f) (Fr t1 \\ xs))).
            { apply IH1. }
            { apply incl_app2.
                { rewrite inter_distrib_app_r. apply incl_appl. apply incl_refl. }
                { rewrite diff_distrib_app_r. apply incl_concat. apply incl_map.
                  apply incl_appl. apply incl_refl. }}
        + apply incl_tran with
            ((Fr t2 /\ xs) ++ concat (map (Fr; f) (Fr t2 \\ xs))).
            { apply IH2. }
            { apply incl_app2.
                { rewrite inter_distrib_app_r. apply incl_appr. apply incl_refl. }
                { rewrite diff_distrib_app_r. apply incl_concat. apply incl_map.
                  apply incl_appr. apply incl_refl. }}
    - apply incl_tran with 
        (remove x (  (Fr t1 /\ (cons x xs)) 
                  ++ concat (map (Fr; f) (Fr t1 \\ (cons x xs))))).
        + apply remove_mon. apply IH1.
        + rewrite remove_diff. rewrite diff_distrib_app_r. apply incl_app2.
            { rewrite remove_diff.
              apply incl_tran with (Fr t1 \\ (x :: nil) /\ (cons x xs)).
                { apply diff_inter_comm. }
                { rewrite inter_cons_not_in_r. 
                    { apply incl_refl. }
                    { intros H. rewrite diff_charac in H. destruct H as [_ H]. 
                      apply H. left. reflexivity. }}}
            { rewrite <- remove_diff. 
              apply incl_tran with (concat (map (Fr; f) (Fr t1 \\ (x :: xs)))).
                { apply remove_incl. }
                { apply incl_concat. apply incl_map. rewrite remove_diff.
                  assert (cons x xs = cons x nil ++ xs) as H1.
                    { reflexivity. }
                  rewrite H1. rewrite diff_distrib_app_l'. apply incl_refl. }}
Qed.

Lemma free_subst : forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v),
    Fr (subst f t) <= concat (map (Fr ; f) (Fr t)).
Proof.
    intros v e f t. unfold subst. rewrite <- (diff_nil v e (Fr t)).
    assert (concat (map (Fr; f) (Fr t \\ nil)) 
      = nil ++ concat (map (Fr; f) (Fr t \\ nil))) as H.
        { reflexivity. } 
    rewrite H. rewrite <- (inter_nil v e (Fr t)) at 2.
    apply free_subst_gen.
Qed.

(*
Lemma free_subst_intersect_gen : 
    forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v) (xs ys:list v), 
       (Fr t /\ xs) == (Fr t /\ ys) ->  subst_ f xs t = subst_ f ys t.
Proof.
    intros v e f. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; 
    intros xs ys H.
    - simpl. simpl in H. 
      destruct (in_dec eqDec x xs) as [H2|H2];
      destruct (in_dec eqDec x ys) as [H3|H3].
        + reflexivity.
        + apply equivNilIsNil in H. inversion H.
        + apply equivSym in H. apply equivNilIsNil in H. 
          inversion H.
        + reflexivity.
    - assert ((Fr t1 /\ xs) == (Fr t1 /\ ys)) as H1.
        { apply inter_sub_equiv with (Fr (App t1 t2)).
            { simpl. apply incl_appl. apply incl_refl. }
            { assumption. } }
      assert ((Fr t2 /\ xs) == (Fr t2 /\ ys)) as H2.
        { apply inter_sub_equiv with (Fr (App t1 t2)).
            { simpl. apply incl_appr. apply incl_refl. }
            { assumption. } }
      simpl. rewrite (IH1 xs ys). rewrite (IH2 xs ys).
        + reflexivity.
        + assumption.
        + assumption.
    -
Show.
*)


