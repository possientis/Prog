Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Image.
Require Import ZF.Class.Inter.
Require Import ZF.Class.InvImage.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Singleton.

(* Inital segment of R on A at a.                                               *)
Definition initSegment (R A:Class) (a:U) : Class
  := A :/\: R^:-1: :[ toClass :{a}: ]:.

Proposition InitSegmentCharac : forall (R A:Class) (a x:U),
  initSegment R A a x <-> A x /\ R :(x,a):.
Proof.
  intros R A a x. split; intros [H1 H2].
  - split. 1: assumption. apply InvImageCharac in H2. destruct H2 as [y [H2 H3]].
    apply SingleCharac in H2. subst. assumption.
  - split. 1: assumption. apply InvImageCharac. exists a. split. 2: assumption.
    apply SingleIn.
Qed.

Proposition InitSegmentWhenEmpty : forall (R A:Class) (a:U),
  initSegment R A a :~: :0: <-> forall x, A x -> ~ R :(x,a):.
Proof.
  intros R A a. split; intros H1.
  - intros x H2 H3. apply EmptyCharac with x. apply H1.
    apply InitSegmentCharac. split; assumption.
  - intros x. split; intros H2.
    + apply InitSegmentCharac in H2. destruct H2 as [H2 H3].
      apply EmptyCharac. assert (H4 := H1 x H2). contradiction.
    + apply EmptyCharac in H2. contradiction.
Qed.

Proposition InitSegmentWhenEmpty1 : forall (R A:Class) (a x:U),
  initSegment R A a :~: :0: -> A x -> ~ R :(x,a):.
Proof.
  intros R A a x H1 H2.
  assert (H3 := proj1 (InitSegmentWhenEmpty R A a) H1 x H2). assumption.
Qed.
