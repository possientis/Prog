Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.OfMinRank.
Require Import ZF.Set.Rank.


Module CEM := Class.Empty.

(* The minimal rank (as a class) of the elements of A.                          *)
Definition minRank (A:Class) : Class := fun x =>
  exists y, y :< ofMinRank A /\ x :< rank y.

Proposition WhenZero : forall (A:Class),
  A :~: :0: -> minRank A :~: :0:.
Proof.
  intros A H1.
  assert (ofMinRank A = :0:) as H2. { apply OfMinRank.WhenZero. assumption. }
  intros x. split; intros H3. 2: contradiction.
  destruct H3 as [y [H3 H4]]. rewrite H2 in H3.
  apply Empty.Charac in H3. contradiction.
Qed.

Proposition IsSmall : forall (A:Class), Small (minRank A).
Proof.
  intros A.
  assert (A :~: :0: \/ A :<>: :0:) as [H1|H1]. { apply LawExcludedMiddle. }
  - assert (minRank A :~: :0:) as H2. { apply WhenZero. assumption. }
    apply Small.EquivCompat with :0:.
    + apply Equiv.Sym. assumption.
    + apply CEM.IsSmall.
  - assert (ofMinRank A <> :0:) as H2. {
      apply OfMinRank.IsNotEmpty. assumption. }
    apply Empty.HasElem in H2. destruct H2 as [y H2].
    assert (Bounded (minRank A)) as H3. {
      exists (rank y). intros x H3. destruct H3 as [z [H3 H4]].
      assert (rank y = rank z) as H5. {
        apply OfMinRank.SameRank with A; assumption. }
      rewrite H5. assumption. }
    apply Bounded.IsSmall. assumption.
Qed.

