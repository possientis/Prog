(* The type 'v' represents the set of variables symbols.        *)
(* The type T v is the set of lambda terms with variables in v. *)

Require Import Eq.
Require Import Identity.
Require Import Composition.
Require Import Extensionality.

Inductive T (v:Type) : Type :=
| Var : v -> T v                    (* variable                 *)
| App : T v -> T v -> T v           (* application              *)
| Lam : v -> T v -> T v             (* lambda abstraction       *)
.

Arguments Var {v} _.
Arguments App {v} _ _.
Arguments Lam {v} _ _.

Fixpoint fmap (v w:Type) (f:v -> w) (t:T v) : T w :=
    match t with
    | Var x     => Var (f x)
    | App t1 t2 => App (fmap v w f t1) (fmap v w f t2)
    | Lam x t1  => Lam (f x) (fmap v w f t1)
    end.

Arguments fmap {v} {w} _ _.

Lemma fmap_id : forall (v:Type), fmap id = @id (T v).  
Proof.
    intros v. apply extensionality.
    induction x as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

Open Scope Composition.  (* for notation ';' *)

Lemma fmap_comp : forall (v w u:Type) (f:v -> w) (g:w -> u),
    fmap (g ; f) = fmap g ; fmap f.
Proof.
    intros v w u f g. apply extensionality.
    induction x as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

(* If equality on v is decidable, then so is equality on T v                    *) 
(* It would seem that the 'right. intros H. inversion H' fragment could be      *)
(* factorized in the below proof, but attempting to do so creates a problem,    *)
(* as the fragment does not fail in branches where it should not be used.       *)
Lemma eq_decidable : forall (v:Type), Eq v -> Eq (T v).
Proof.
    intros v eq s t. revert s t.
    induction s as [x|s1 IH1 s2 IH2|x s1 IH1];
    destruct t as [y|t1 t2|y t1].
    - destruct (eq x y) as [E|E].
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
    - destruct (eq x y) as [E|E], (IH1 t1) as [E1|E1].
        + subst. left. reflexivity.
        + right. intros H. inversion H. subst. apply E1. reflexivity.
        + right. intros H. inversion H. subst. apply E.  reflexivity.
        + right. intros H. inversion H. subst. apply E.  reflexivity.
Qed.

Arguments eq_decidable {v} _.

