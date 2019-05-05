(* The type 'v' represents the set of variables symbols.        *)
(* The type T v is the set of lambda terms with variables in v. *)

Require Import identity.
Require Import composition.
Require Import extensionality.

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

Open Scope composition.  (* for notation ';' *)

Lemma fmap_comp : forall (v w u:Type) (f:v -> w) (g:w -> u),
    fmap (g ; f) = fmap g ; fmap f.
Proof.
    intros v w u f g. apply extensionality.
    induction x as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

