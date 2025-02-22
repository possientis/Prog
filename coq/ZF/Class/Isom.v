Require Import ZF.Class.
Require Import ZF.Class.Bij.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.InitSegment.
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

(* The direct image by an isomorphism of an inital segment is an inital segment.*)
Proposition IsomInitSegmentImage : forall (F R S A B C:Class) (a:U),
  Isom F R S A B    ->
  C :<=: A          ->
  A a               ->
  F:[initSegment R C a]: :~: initSegment S F:[C]: (F!a).
Proof.
  intros F R S A B C a [H1 H2] H3 H4 y. split; intros H5.
  - apply (proj1 (ImageCharac _ _ _)) in H5. destruct H5 as [x [H5 H6]].
    apply InitSegmentCharac in H5. destruct H5 as [H5 H7].
    apply InitSegmentCharac. assert (F!x = y) as H8. {
      apply (BijEval F A B); try assumption. apply H3. assumption. }
    split.
    + apply ImageCharac. exists x. split; assumption.
    + rewrite <- H8. apply H2; try assumption. apply H3. assumption.
  - apply InitSegmentCharac in H5. destruct H5 as [H5 H6].
    apply (proj1 (ImageCharac _ _ _)) in H5. destruct H5 as [x [H5 H7]].
    assert (F!x = y) as H8. {
      apply (BijEval F A B); try assumption. apply H3. assumption. }
    apply ImageCharac. exists x. split. 2: assumption.
    apply InitSegmentCharac. split. 1: assumption. apply H2. 2: assumption.
    + apply H3. assumption.
    + rewrite H8. assumption.
Qed.

Proposition IsomFullInitSegmentImage : forall (F R S A B:Class) (a:U),
  Isom F R S A B    ->
  A a               ->
  F:[initSegment R A a]: :~: initSegment S B (F!a).
Proof.
  intros F R S A B a H1 H2.
  apply ClassEquivTran with (initSegment S F:[A]: F!a).
  - apply IsomInitSegmentImage with A B; try assumption. apply InclRefl.
  - apply InitSegmentEquivCompatR, BijDomainImage, IsomIsBij with R S. assumption.
Qed.

Proposition IsomEmptyInitSegment : forall (F R S A B C:Class) (a:U),
  Isom F R S A B                    ->
  C :<=: A                          ->
  A a                               ->
  initSegment R C a :~: :0:         ->
  initSegment S F:[C]: F!a :~: :0:.
Proof.
  intros F R S A B C a H1 H2 H3 H4.
  apply ClassEquivTran with F:[initSegment R C a]:.
  - apply ClassEquivSym, IsomInitSegmentImage with A B; assumption.
  - apply ImageOfEmpty. assumption.
Qed.
