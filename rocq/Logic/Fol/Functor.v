(* The type 'v' represents the set of variables symbols.        *)
(* The type P v is the set of set theoretic first order         *)
(* propositions with variables in v.                            *)

Require Import Logic.Fol.Syntax.

Require Import Logic.Func.Identity.
Require Import Logic.Func.Composition.

Require Import Logic.Axiom.Extensionality.

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

(* Appears convenient for real use.                                             *)
Lemma fmap_comp' : forall (v w u:Type) (f:v -> w) (g:w -> u) (p:P v),
    fmap (g ; f) p = fmap g (fmap f p).
Proof.
    intros v w u f g p. change (fmap (g ; f) p = (fmap g ; fmap f) p).
    rewrite fmap_comp. reflexivity.
Qed.
