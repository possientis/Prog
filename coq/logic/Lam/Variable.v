Require Import List.

Require Import In.
Require Import Eq.
Require Import Permute.
Require Import Replace.
Require Import Coincide.
Require Import Composition.
Require Import Lam.T.

(* We do not have sets: the variables of a term are a list, not a set.          *)

Fixpoint var (v:Type) (t:T v) : list v :=
    match t with
    | Var x     => cons x nil
    | App t1 t2 => var v t1 ++ var v t2
    | Lam x t1  => cons x  (var v t1)
    end.

Arguments var {v} _.


Lemma var_fmap : forall (v w:Type) (f:v -> w) (t:T v),
    var (fmap f t) = map f (var t).
Proof.
    intros v w f.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite map_app, IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

(* If two functions f g coincide on the variables of a term t, then the terms   *)
(* fmap f t and fmap g t are equal, and conversely.                             *)
Lemma var_support : forall (v w:Type) (f g:v -> w) (t:T v),
    coincide (var t) f g  <-> fmap f t = fmap g t.
Proof.
    intros v w f g. unfold coincide. 
    induction t as [x|t1 [IH1 IH1'] t2 [IH2 IH2']|x t1 [IH1 IH1']]; simpl; split.
    - intros H. rewrite H.
        + reflexivity.
        + left. reflexivity.
    - intros H. inversion H as [H']. clear H. intros y [H|H].
        + subst. assumption.
        + exfalso. assumption.
    - intros H. rewrite IH1, IH2.
        + reflexivity.
        + intros x H'. apply H. apply in_or_app. right. assumption.
        + intros x H'. apply H. apply in_or_app. left.  assumption.
    - intros H. inversion H. intros x H'. apply in_app_or in H'.
      destruct H' as [H'|H']. 
        + apply IH1'; assumption.
        + apply IH2'; assumption.
    - intros H. rewrite IH1.
        + rewrite (H x). { reflexivity. } { left. reflexivity. }
        + intros y H'.  apply H. right. assumption.
    - intros H. inversion H. intros y [H'|H'].
        + subst. assumption.
        + apply IH1'; assumption.
Qed.

Lemma var_permute_replace : forall (v:Type) (e:Eq v) (x y:v) (t:T v),
    ~ y :: var t -> fmap (y // x) t = fmap (y <:> x) t.
Proof.
    intros v e x y t H. apply var_support, permute_replace. assumption.
Qed.

Lemma var_replace_trans : forall (v:Type) (e:Eq v) (x y z:v) (t:T v),
    ~ y :: var t -> 
    fmap (z // y) (fmap (y // x) t) = fmap (z // x) t.
Proof.
    intros v e x y z t H. 
    remember (z // y) as g eqn:Eg. 
    remember (y // x) as f eqn:Ef. 
    fold ((fmap g ; fmap f) t). rewrite <- fmap_comp. 
    apply var_support.
    rewrite Eg, Ef. apply replace_trans.
    assumption. 
Qed.
    

Lemma var_replace_remove : forall (v:Type) (e:Eq v) (x y:v) (t:T v),
    x <> y -> ~ x :: var (fmap (y // x) t).
Proof.
    intros v e x y t E H. rewrite var_fmap in H.
    apply in_map_iff in H. destruct H as [u [H1 H2]].
    destruct (eqDec u x) as [H'|H'].
    - subst. rewrite replace_x in H1. apply E. symmetry. assumption.
    - rewrite replace_not_x in H1.
        + apply H'. assumption.
        + assumption.
Qed.

