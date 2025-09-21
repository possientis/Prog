Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.FinalSegment.
Require Import ZF.Class.Order.Maximal.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* The successor (as a class) in the ordered class (A,R) of a set a.            *)
Definition succ (R A:Class) (a:U) : Class := fun x =>
  exists y, x :< y /\ Minimal R (finalSegment R A a) y.

Proposition Charac : forall (R A:Class) (a x:U), succ R A a x <-> exists y,
  x :< y                                    /\
  A y                                       /\
  R :(a,y):                                 /\
  forall z, A z -> R :(a,z): -> ~ R :(z,y):.
Proof.
  intros R A a x. split; intros H1.
  - destruct H1 as [y [H1 H2]].
    assert (finalSegment R A a y) as H3. {
      apply Minimal.IsIn with R. assumption. }
    assert (A y) as H4. { apply FinalSegment.WhenIn with R a. assumption. }
    assert (R :(a,y):)  as H5. { apply FinalSegment.IsMore with A. assumption. }
    exists y. split. 1: assumption. split. 1: assumption. split. 1: assumption.
    intros z H6 H7 H8. destruct H2 as [H2 H9]. apply H9 with z. 2: assumption.
    apply FinalSegment.Charac. split; assumption.
  - destruct H1 as [y [H1 [H2 [H3 H4]]]]. exists y. split. 1: assumption.
    remember (finalSegment R A a) as B eqn:H5. split.
    + rewrite H5. apply FinalSegment.Charac. split; assumption.
    + intros z H6. apply H4; rewrite H5 in H6.
      * apply FinalSegment.WhenIn in H6. assumption.
      * apply FinalSegment.IsMore with A. assumption.
Qed.

Proposition WhenMaximal : forall (R A:Class) (a:U),
  Maximal R A a -> succ R A a :~: :0:.
Proof.
  intros R A a H1. intros x. split; intros H2.
  - destruct H2 as [y [H2 H3]]. apply Minimal.IsIn in H3.
    assert (A y) as H4. { apply FinalSegment.WhenIn with R a. assumption. }
    apply FinalSegment.IsMore in H3. destruct H1 as [H1 H5].
    exfalso. apply H5 with y; assumption.
  - contradiction.
Qed.

Proposition WhenNotMaximal : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A                        ->
  A a                                           ->
  ~ Maximal R A a                               ->
  exists b,
    toClass b :~: succ R A a                    /\
    A b                                         /\
    R :(a,b):                                   /\
    forall x, A x -> R :(a,x): -> ~ R :(x,b):.
Proof.
  intros R A a H1 H2 H3.
  remember (finalSegment R A a) as B eqn:H4.
  assert (B :<>: :0:) as H5. {
    intros H5. apply H3, Maximal.EmptySegment. split.
    1: assumption. rewrite <- H4. assumption. }
  assert (B :<=: A) as H6. { rewrite H4. apply FinalSegment.IsIncl. }
  assert (exists b, Minimal R B b) as H7. {
    apply WellFoundedWellOrd.HasMinimal with A; assumption. }
  destruct H7 as [b H7]. exists b. split.
  - intros x. split; intros H8.
    + exists b. split. 1: assumption. rewrite <- H4. assumption.
    + destruct H8 as [c [H8 H9]]. rewrite <- H4 in H9.
      assert (b = c) as H10. {
        apply (Minimal.Unique R A B); try assumption.
        apply H1. }
      subst. assumption.
  - assert (B b) as H8. { apply Minimal.IsIn with R. assumption. }
    assert (R :(a,b):) as H9. {
      rewrite H4 in H8. apply FinalSegment.IsMore with A. assumption. }
    split. 1: apply H6, H8. split. 1: assumption.
    intros x H10 H11. destruct H7 as [H7 H12]. apply H12.
    rewrite H4. apply FinalSegment.Charac. split; assumption.
Qed.

Proposition IsSmall : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A  ->
  A a                     ->
  Small (succ R A a).
Proof.
  intros R A a H1 H2.
  assert (Maximal R A a \/ ~Maximal R A a) as H3. { apply LawExcludedMiddle. }
  destruct H3 as [H3|H3].
  - apply Small.EquivCompat with :0:.
    + apply Equiv.Sym, WhenMaximal. assumption.
    + apply Empty.IsSmall.
  - apply WhenNotMaximal in H3; try assumption.
    destruct H3 as [b [H3 _]]. exists b. assumption.
Qed.
