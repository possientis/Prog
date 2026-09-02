Section Declaration.
  Variable n : nat.
  Hypothesis Pos_n : (gt n 0).
  Definition one := S 0.
  Definition two : nat := S one.
  Definition three := S two : nat.
  Definition double (m:nat) := plus m m.
  Definition double' := fun m:nat => plus m m.
  Definition add_n (m:nat) := plus m n.

End Declaration.

Section Minimal_Logic.
  Variable A B C : Prop.
  Definition Ax1 := (A -> (B -> C)) -> (A -> B) -> (A -> C). 
  Goal Ax1.
  unfold Ax1.
  intro H.
  intros H' HA.
  apply H.
  exact HA.
  apply H'.
  assumption.

  Save trivial_lemma.

  Lemma distr_impl: (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
    intros.
    apply H; [ assumption | apply H0; assumption ].
  Qed.

  Lemma distr_impl': (A -> B -> C) -> (A -> B) -> (A -> C).
    auto.
  Qed.

  Inspect 5.

  Lemma and_commutative : A/\B -> B/\A.
    intro H; elim H; auto.
  Qed.

  Lemma or_commutative: A\/B -> B\/A.
    intro H; elim H.
    intro HA.
    clear H.
    clear C.
    right.
    assumption.
    auto.
  Restart.
    tauto.
  Qed.

  Lemma distr_and : (A -> B/\C) -> (A -> B) /\ (A -> C).
    tauto.
  Qed.

  Lemma Peirce : ((A -> B) -> A) -> A.
    try tauto.
  Abort.

  Lemma NNPeirce : ~~(((A -> B) -> A) -> A).
    tauto.
  Qed.


  Require Import Classical.

  Lemma Peirce : ((A -> B) -> A) -> A.
    apply NNPP; tauto.
  Qed.

  Section club.

  Variables Scottish RedSocks WearKilt Married GoOutSunday : Prop.
  Hypothesis rule1 : ~Scottish -> RedSocks.
  Hypothesis rule2 : WearKilt \/ ~RedSocks.
  Hypothesis rule3 : Married -> ~GoOutSunday.
  Hypothesis rule4 : GoOutSunday <-> Scottish.
  Hypothesis rule5 : WearKilt -> Scottish/\Married.
  Hypothesis rule6 : Scottish -> WearKilt.

  Lemma NoMember : False.
    tauto.
  Qed.

  End club.









