Require Import ZF.Class.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.BijectionOn.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Range.
Require Import ZF.Class.Restrict.
Require Import ZF.Set.
Require Import ZF.Set.Eval.

(* F is a bijection from A to B.                                                *)
Definition Bij (F A B:Class) : Prop := BijectionOn F A /\ range F :~: B.

Proposition ConverseIsBij : forall (F A B:Class),
  Bij F A B -> Bij F^:-1: B A.
Proof.
  intros F A B [[H1 H2] H3]. split.
  - split.
    + apply ConverseIsBijection. assumption.
    + apply ClassEquivTran with (range F). 2: assumption. apply ConverseDomain.
  - apply ClassEquivTran with (domain F). 2: assumption. apply ConverseRange.
Qed.

Proposition ComposeIsBij : forall (F G A B C:Class),
  Bij F A B -> Bij G B C -> Bij (G :.: F) A C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply ComposeIsBijectionOn with B; try assumption.
    apply DoubleInclusion, ClassEquivSym. assumption.
  - apply ClassEquivTran with (range G). 2: assumption.
    apply ComposeRangeIsSame. destruct H3 as [H3 H5].
    apply InclTran with B.
    + apply DoubleInclusion, ClassEquivSym. assumption.
    + apply DoubleInclusion. assumption.
Qed.

Proposition BijFEvalIsInRange : forall (F A B:Class) (x:U),
  Bij F A B -> A x -> B (F!x).
Proof.
  intros F A B x [H1 H2] H3. apply H2.
  apply BijectionOnFEvalIsInRange with A; assumption.
Qed.

Proposition BijF_EvalIsInDomain : forall (F A B:Class) (y:U),
  Bij F A B -> B y -> A (F^:-1:!y).
Proof.
  intros F A B y H1 H2. apply BijFEvalIsInRange with B. 2: assumption.
  apply ConverseIsBij. assumption.
Qed.

Proposition BijF_FEval : forall (F A B:Class) (x:U),
  Bij F A B -> A x -> F^:-1:!(F!x) = x.
Proof.
  intros F A B x [H1 H2]. apply BijectionOnF_FEval. assumption.
Qed.

Proposition BijFF_Eval : forall (F A B:Class) (y:U),
  Bij F A B -> B y -> F!(F^:-1:!y) = y.
Proof.
  intros F A B y [H1 H2] H3. apply BijectionOnFF_Eval with A. 1: assumption.
  apply H2. assumption.
Qed.

