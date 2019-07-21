Require Import List.
Import ListNotations.

Require Import Eq.

Require Import Lam.T.
Require Import Lam.Free.
Require Import Lam.Variable.

Fixpoint bnd (v:Type) (t:T v) : list v :=
    match t with
    | Var x     => []
    | App t1 t2 => bnd v t1 ++ bnd v t2
    | Lam x t1  => x :: bnd v t1
    end.


Arguments bnd {v} _.

(*
Lemma bnd_free : forall (v:Type) (e:Eq v) (t:T v) (z:v),
    In z (var t) <-> In z (free e t) \/ In z (bnd t).
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
                { destruct (e x z) as [E|E].
                    { right. simpl. left. assumption. }
                    { left.  simpl.
   


Show.
*)
