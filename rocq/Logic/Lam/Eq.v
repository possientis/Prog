Require Import Logic.Class.Eq.
Require Import Logic.Lam.Syntax.


(* If equality on v is decidable, then so is equality on T v                    *) 
Lemma eqDecidable : forall (v:Type) (e:Eq v), 
    forall (s t:T v), {s = t} + {s <> t}.
Proof.
    intros v e.
    induction s as [x|s1 IH1 s2 IH2|x s1 IH1];
    destruct t as [y|t1 t2|y t1].
    - destruct (eqDec x y) as [E|E].
        + subst. left. reflexivity.
        + right. intros H. inversion H. subst. apply E. reflexivity.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - destruct (IH1 t1) as [E1|E1], (IH2 t2) as [E2|E2].
        + subst. left. reflexivity.
        + right. intros H. inversion H. subst. apply E2. reflexivity.
        + right. intros H. inversion H. subst. apply E1. reflexivity.
        + right. intros H. inversion H. subst. apply E1. reflexivity.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - destruct (eqDec x y) as [E|E], (IH1 t1) as [E1|E1].
        + subst. left. reflexivity.
        + right. intros H. inversion H. subst. apply E1. reflexivity.
        + right. intros H. inversion H. subst. apply E.  reflexivity.
        + right. intros H. inversion H. subst. apply E.  reflexivity.
Defined.

Arguments eqDecidable {v} {e}.

Global Instance EqT (v:Type) (e:Eq v) : Eq (T v) := { eqDec := eqDecidable }.
