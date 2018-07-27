Require Import eq.
Require Import identity.
Require Import composition.
Require Import term.
Require Import permute.

(* will turn 'P' into a functor *)
Fixpoint vmap (v w:Type) (f:v -> w) (t:P v) : P w :=
    match t with
    | Var x     => Var (f x)
    | App t1 t2 => App (vmap v w f t1) (vmap v w f t2)
    | Lam x t1  => Lam (f x) (vmap v w f t1)
    end.

Arguments vmap {v} {w} _ _.

(* syntactic sugar *)
Definition swap (v:Type) (p:Eq v) (x y:v) : P v -> P v := vmap (permute p x y).

Arguments swap {v} _ _ _ _.

Lemma vmap_id : forall (v:Type) (t:P v), vmap id t = t. 
Proof.
    intros v t. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity. 
Qed.

Open Scope composition.

Lemma vmap_comp : forall (v w u:Type) (f:v -> w) (g:w -> u) (t:P v),
    vmap (g ; f) t = vmap g (vmap f t).
Proof.
    intros v w u f g t. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.





