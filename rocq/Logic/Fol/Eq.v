Require Import Logic.Class.Eq.
Require Import Logic.Fol.Syntax.


(* If equality on v is decidable, then so is equality on P v                    *) 
Lemma eqDecidable : forall (v:Type) (e:Eq v),
    forall (s t:P v), {s = t} + {s <> t}.
Proof.
    intros v e.
    induction s as [|x y|s1 IH1 s2 IH2|x s1 IH1];
    destruct t as [|x' y'|t1 t2|x' t1].
    - left. reflexivity.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - destruct (eqDec x x') as [Ex|Ex], (eqDec y y') as [Ey|Ey].
        + subst. left. reflexivity.
        + right. intros H. inversion H. subst. apply Ey. reflexivity.
        + right. intros H. inversion H. subst. apply Ex. reflexivity.
        + right. intros H. inversion H. subst. apply Ex. reflexivity.
    - right. intros H. inversion H.
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
    - right. intros H. inversion H.
    - destruct (eqDec x x') as [E|E], (IH1 t1) as [E1|E1].
        + subst. left. reflexivity.
        + right. intros H. inversion H. subst. apply E1. reflexivity.
        + right. intros H. inversion H. subst. apply E.  reflexivity.
        + right. intros H. inversion H. subst. apply E.  reflexivity.
Defined.

Arguments eqDecidable {v} {e}.

Global Instance EqP (v:Type) (e:Eq v) : Eq (P v) := { eqDec := eqDecidable }.
