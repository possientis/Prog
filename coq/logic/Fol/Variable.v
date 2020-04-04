Require Import List.

Require Import In.
Require Import Eq.
Require Import Map.
Require Import Permute.
Require Import Replace.
Require Import Coincide.
Require Import Composition.
Require Import Fol.P.

(* We do not have sets: the variables of a formula are a list, not a set.       *)

Fixpoint var (v:Type) (p:P v) : list v :=
    match p with
    | Bot       => nil
    | Elem x y  => cons x (cons y nil)
    | Imp p1 p2 => var v p1 ++ var v p2
    | All x p1  => cons x (var v p1)
    end.

Arguments var {v} _.


Lemma var_fmap : forall (v w:Type) (f:v -> w) (p:P v),
    var (fmap f p) = map f (var p).
Proof.
    intros v w f.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite map_app, IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

(* If two functions f g coincide on the variables of a formula p, then the      *)
(* formulas fmap f t and fmap g t are equal, and conversely.                    *)
Lemma var_support : forall (v w:Type) (f g:v -> w) (p:P v),
    coincide (var p) f g  <-> fmap f p = fmap g p.
Proof.
    intros v w f g. unfold coincide. 
    induction p as [|x y|p1 [IH1 IH1'] p2 [IH2 IH2']|x p1 [IH1 IH1']]; 
    simpl; split.
    - intros. reflexivity.
    - intros. exfalso. assumption.
    - intros H. rewrite (H x), (H y).
        + reflexivity.
        + right. left. reflexivity.
        + left. reflexivity.
    - intros H. inversion H. intros z [H'|[H'|H']].
        + subst. assumption.
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

Lemma var_permute_replace : forall (v:Type) (e:Eq v) (x y:v) (p:P v),
    ~ y :: var p -> fmap (y // x) p = fmap (y <:> x) p.
Proof.
    intros v e x y t H. apply var_support, permute_replace. assumption.
Qed.

Lemma var_replace_trans : forall (v:Type) (e:Eq v) (x y z:v) (t:P v),
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

Lemma var_replace_remove : forall (v:Type) (e:Eq v) (x y:v) (p:P v),
    x <> y -> ~ x :: var (fmap (y // x) p).
Proof.
    intros v e x y p E H. rewrite var_fmap in H.
    apply mapIn in H. destruct H as [u [H1 H2]].
    destruct (eqDec u x) as [H'|H'].
    - subst. rewrite replace_x in H2. apply E. assumption.
    - rewrite replace_not_x in H2.
        + apply H'. symmetry. assumption.
        + assumption.
Qed.  
