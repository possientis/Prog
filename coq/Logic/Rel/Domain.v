Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Coreflexive.

(* Domain of a relation defined as coreflexive relation rather than set         *)
Inductive dom (a b:Type) (r:R a b) : Rel a :=
| mkDom : forall (x:a), (exists (y:b), r x y) -> dom a b r x x
.

Arguments dom {a} {b}.

Lemma dom_corefl : forall (a b:Type) (r:R a b), coreflexive (dom r).
Proof.
    unfold coreflexive. intros a b r. apply incl_charac. intros x y H1.
    destruct H1. constructor.
Qed.
