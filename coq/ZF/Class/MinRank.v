Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.OfMinRank.
Require Import ZF.Set.Rank.


Module CEM := Class.Empty.


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
  -
Admitted.

