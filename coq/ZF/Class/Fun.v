Declare Scope ZF_Class_Fun_scope.
Open    Scope ZF_Class_Fun_scope.

Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Incl.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Range.
Require Import ZF.Set.
Require Import ZF.Set.Eval.

(* F is a function from A to B.                                                 *)
Definition Fun (F A B:Class) : Prop := FunctionOn F A /\ range F :<=: B.

Notation "F :: A :-> B" := (Fun F A B)
  (at level 0, no associativity) : ZF_Class_Fun_scope.

Proposition FunFEvalIsInRange : forall (F A B:Class) (x:U),
  (F :: A :-> B) -> A x -> B (F!x).
Proof.
  intros F A B x [H1 H2] H3. apply H2.
  apply FunctionOnFEvalIsInRange with A; assumption.
Qed.

Proposition ComposeIsFun : forall (F G A B C: Class),
  F :: A :-> B ->
  G :: B :-> C ->
  (G :.: F) :: A :-> C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply ComposeIsFunctionOn with B; assumption.
  - apply InclTran with (range G). 2: assumption. apply ComposeRangeIsSmaller.
Qed.
