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

Proposition IsomIsBij : forall (F R S A B:Class),
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
      * apply BijEvalIsInDomain with B; assumption.
      * apply BijEvalIsInDomain with B; assumption.
      * rewrite (BijFF_Eval F A B x), (BijFF_Eval F A B y); assumption.
    + rewrite <- (BijFF_Eval F A B x), <- (BijFF_Eval F A B y); try assumption.
      apply H2. 3: assumption.
      * apply BijEvalIsInDomain with B; assumption.
      * apply BijEvalIsInDomain with B; assumption.
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
    + rewrite (BijComposeEval F G A B C x); try assumption.
      rewrite (BijComposeEval F G A B C y); try assumption.
      apply H4. 3: apply H2; try assumption.
      * apply BijEvalIsInRange with A; assumption.
      * apply BijEvalIsInRange with A; assumption.
    + apply H2; try assumption. apply H4.
      * apply BijEvalIsInRange with A; assumption.
      * apply BijEvalIsInRange with A; assumption.
      * rewrite (BijComposeEval F G A B C x) in H7; try assumption.
        rewrite (BijComposeEval F G A B C y) in H7; try assumption.
Qed.
