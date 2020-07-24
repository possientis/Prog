Require Import List.
Import ListNotations.

Require Import Logic.Class.Eq.

Require Import Logic.List.In.
Require Import Logic.List.Remove.
Require Import Logic.List.Include.

Require Import Logic.Lam.Free.
Require Import Logic.Lam.Syntax.
Require Import Logic.Lam.Functor.
Require Import Logic.Lam.Variable.

Fixpoint bnd (v:Type) (t:T v) : list v :=
    match t with
    | Var x     => []
    | App t1 t2 => bnd v t1 ++ bnd v t2
    | Lam x t1  => x :: bnd v t1
    end.

Arguments bnd {v} _.

Lemma bnd_var : forall (v:Type) (t:T v), bnd t <= var t.
Proof.
    intros v.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - intros z H. inversion H.
    - apply incl_app2; assumption.
    - apply incl_cons2. assumption.
Qed.

Lemma bnd_free : forall (v:Type) (e:Eq v) (t:T v) (z:v),
    z :: var t <-> (z :: Fr t) \/ (z :: bnd t).
Proof.
    intros v e t z. split.
    - induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros H; simpl in H.
        + left. simpl. assumption.
        + apply in_app_or in H. destruct H as [H|H].
            { apply IH1 in H. destruct H as [H|H].
                { left.  simpl. apply in_or_app. left. assumption. }
                { right. simpl. apply in_or_app. left. assumption. }
            }
            { apply IH2 in H. destruct H as [H|H].
                { left.  simpl. apply in_or_app. right. assumption. }
                { right. simpl. apply in_or_app. right. assumption. }
            }
        + destruct H as [H|H].
            { right. simpl. left. assumption. }
            { apply IH1 in H. destruct H as [H|H].
                { destruct (eqDec x z) as [E|E].
                    { right. simpl. left. assumption. }
                    { left.  simpl. apply remove_charac. split; assumption. }
                }
                { right. right. assumption. } 
            } 
    - intros [H|H].
        + apply (free_var v e). assumption.
        + apply bnd_var. assumption.
Qed.

Lemma bnd_fmap : forall (v w:Type) (f:v -> w) (t:T v),
    bnd (fmap f t) = map f (bnd t).
Proof.
    intros v w f.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite map_app, IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.
