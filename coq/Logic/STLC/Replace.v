Require Import Logic.Class.Eq.

Require Import Logic.STLC.Syntax.

Definition replace (b v:Type) (e:Eq v) (x:v) (t:Exp b v) (u:v) : Exp b v :=
    match eqDec u x with
    | left _    => t
    | right _   => Var u
    end.

Arguments replace {b} {v} {e}.

Notation "t // x" := (replace x t)
    (at level 70, no associativity) : STLC_Replace_scope.

Open Scope STLC_Replace_scope.

Lemma replace_x : forall (b v:Type) (e:Eq v) (x:v) (t:Exp b v),
    (t // x) x = t.
Proof.
    intros b v e x t. unfold replace. destruct (eqDec x x) as [H1|H1].
    - reflexivity.
    - exfalso. apply H1. reflexivity.
Qed.


