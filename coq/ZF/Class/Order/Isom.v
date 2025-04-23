Require Import ZF.Class.
Require Import ZF.Class.Bij.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* F is an (R,S)-isomorphism from A to B.                                       *)
Definition Isom (F R S A B:Class) : Prop := Bij F A B /\ forall x y, A x -> A y ->
  R :(x,y): <-> S :(F!x,F!y):.

(* An isomorphism is a bijection.                                               *)
Proposition IsBij : forall (F R S A B:Class),
  Isom F R S A B -> Bij F A B.
Proof.
  intros F R S A B [H1 _]. assumption.
Qed.

(* If F:A -> B is an (R,S)-isomorphism, F^-1 : B -> A is an (S,R)-isomorpshism. *)
Proposition ConverseIsIsom : forall (F R S A B:Class),
  Isom F R S A B -> Isom F^:-1: S R B A.
Proof.
  intros F R S A B [H1 H2]. split.
  - apply ConverseIsBij. assumption.
  - intros x y H3 H4. split; intros H5.
    + apply H2.
      * apply Bij.ConverseEvalIsInDomain with B; assumption.
      * apply Bij.ConverseEvalIsInDomain with B; assumption.
      * rewrite (Bij.EvalOfConverseEval F A B x), (Bij.EvalOfConverseEval F A B y);
        assumption.
    + rewrite <- (Bij.EvalOfConverseEval F A B x), <- (Bij.EvalOfConverseEval F A B y);
      try assumption. apply H2. 3: assumption.
      * apply Bij.ConverseEvalIsInDomain with B; assumption.
      * apply Bij.ConverseEvalIsInDomain with B; assumption.
Qed.

(* The composition of two isomorpshims is an isomorphism.                       *)
Proposition ComposeIsIsom : forall (F G R S T A B C:Class),
  Isom F R S A B ->
  Isom G S T B C ->
  Isom (G :.: F) R T A C.
Proof.
  intros F G R S T A B C [H1 H2] [H3 H4]. split.
  - apply ComposeIsBij with B; assumption.
  - intros x y H5 H6. split; intros H7.
    + rewrite (Bij.ComposeEval F G A B C x); try assumption.
      rewrite (Bij.ComposeEval F G A B C y); try assumption.
      apply H4. 3: apply H2; try assumption.
      * apply Bij.EvalIsInRange with A; assumption.
      * apply Bij.EvalIsInRange with A; assumption.
    + apply H2; try assumption. apply H4.
      * apply Bij.EvalIsInRange with A; assumption.
      * apply Bij.EvalIsInRange with A; assumption.
      * rewrite (Bij.ComposeEval F G A B C x) in H7; try assumption.
        rewrite (Bij.ComposeEval F G A B C y) in H7; try assumption.
Qed.

(* Transporting a 'relation R on A' by F.                                       *)
Definition transport (F R A:Class) : Class := fun x =>
  exists y z, x = :(F!y,F!z): /\ A y /\ A z /\ R :(y,z):.

Proposition TransportCharac2F : forall (F R A B:Class) (y z:U),
  Bij F A B ->
  A y       ->
  A z       ->
  transport F R A :(F!y,F!z): <-> A y /\ A z /\ R :(y,z):.
Proof.
  intros F R A B y z H1 H2 H3. split; intros H4.
  - destruct H4 as [y' [z' [H4 [H5 [H6 H7]]]]]. apply OrdPairEqual in H4.
    destruct H4 as [H4 H8].
    assert (y = y') as H9.  { apply Bij.EvalInjective with F A B; assumption. }
    assert (z = z') as H10. { apply Bij.EvalInjective with F A B; assumption. }
    subst. split. 1: assumption. split; assumption.
  - destruct H4 as [H4 [H5 H6]]. exists y. exists z. split.
    1: reflexivity. split. 1: assumption. split; assumption.
Qed.

Proposition FromTransport : forall (F R S A B:Class),
  (S = transport F R A) -> Bij F A B -> Isom F R S A B.
Proof.
  intros F R S A B H1 H2. split. 1: assumption.
  intros x y H3 H4. split; intros H5.
  - rewrite H1. apply (TransportCharac2F F R A B); try assumption.
    split. 1: assumption. split; assumption.
  - rewrite H1 in H5. apply (TransportCharac2F F R A B) in H5; try assumption.
    destruct H5 as [_ [_ H5]]. assumption.
Qed.

