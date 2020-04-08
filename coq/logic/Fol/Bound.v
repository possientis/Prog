Require Import List.
Import ListNotations.

Require Import In.
Require Import Eq.
Require Import Remove.
Require Import Include.

Require Import Fol.P.
Require Import Fol.Free.
Require Import Fol.Variable.

Fixpoint bnd (v:Type) (p:P v) : list v :=
    match p with
    | Bot       => []
    | Elem x y  => []
    | Imp p1 p2 => bnd v p1 ++ bnd v p2
    | All x p1  => x :: bnd v p1
    end.

Arguments bnd {v} _.

Lemma bnd_var : forall (v:Type) (p:P v), bnd p <= var p.
Proof.
    intros v.
    induction p as [|x y|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - apply incl_refl.
    - intros z H. inversion H.
    - apply incl_app2; assumption.
    - apply incl_cons2. assumption.
Qed.

Lemma bnd_free : forall (v:Type) (e:Eq v) (p:P v) (z:v),
    z :: var p <-> (z :: Fr p) \/ (z :: bnd p).
Proof.
    intros v e p z. split.
    - induction p as [|x y|t1 IH1 t2 IH2|x t1 IH1]; intros H; simpl in H.
        + exfalso. assumption.
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

Lemma bnd_fmap : forall (v w:Type) (f:v -> w) (p:P v),
    bnd (fmap f p) = map f (bnd p).
Proof.
    intros v w f.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite map_app, IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.
