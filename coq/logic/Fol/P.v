(* The type 'v' represents the set of variables symbols.        *)
(* The type P v is the set of set theoretic first order         *)
(* propositions with variables in v.                            *)

Require Import Eq.
Require Import Identity.
Require Import Composition.
Require Import Extensionality.

Inductive P (v:Type) : Type :=
| Bot  : P v                        (* bottom                   *)
| Elem : v -> v -> P v              (* x `Elem` y               *)
| Imp  : P v -> P v -> P v          (* implication              *)
| All  : v -> P v -> P v            (* quantification           *)
.

Arguments Bot  {v}.
Arguments Elem {v} _ _.
Arguments Imp  {v} _ _.
Arguments All  {v} _ _.

Fixpoint fmap (v w:Type) (f:v -> w) (p:P v) : P w :=
    match p with
    | Bot       => Bot
    | Elem x y  => Elem (f x) (f y)
    | Imp p1 p2 => Imp (fmap v w f p1) (fmap v w f p2)
    | All x p1  => All (f x) (fmap v w f p1)
    end.

Arguments fmap {v} {w} _ _.

Lemma fmap_id : forall (v:Type), fmap id = @id (P v).
Proof.
    intros v. apply extensionality.
    induction x as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.


Lemma fmap_comp : forall (v w u:Type) (f:v -> w) (g:w -> u),
    fmap (g ; f) = fmap g ; fmap f.
Proof.
    intros v w u f g. apply extensionality.
    induction x as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.


(* If equality on v is decidable, then so is equality on P v                    *) 
Lemma eqDecidable : forall (v:Type) (e:Eq v),
    forall (s t:P v), {s = t} + {s <> t}.
Proof.
    intros v e s t. revert s t.
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


Instance EqP (v:Type) (e:Eq v) : Eq (P v) := { eqDec := eqDecidable }.


