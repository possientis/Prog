Require Import Logic.Class.Eq.

Require Import Logic.STLC.Syntax.

Declare Scope STLC_Replace_scope.

Definition replace (b v:Type) (eq:Eq v) (x:v) (e:Exp b v) (u:v) : Exp b v :=
    match eqDec u x with
    | left _    => e
    | right _   => Var u
    end.

Arguments replace {b} {v} {eq}.

Notation "e // x" := (replace x e)
    (at level 70, no associativity) : STLC_Replace_scope.

Open Scope STLC_Replace_scope.

Lemma replace_x : forall (b v:Type) (eq:Eq v) (x:v) (e:Exp b v),
    (e // x) x = e.
Proof.
    intros b v eq x e. unfold replace. destruct (eqDec x x) as [H1|H1].
    - reflexivity.
    - exfalso. apply H1. reflexivity.
Qed.


