Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter2.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.RestrictOfClass.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CEM := ZF.Class.Empty.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.

(* The cardinal of a set is the smallest ordinal in bijection with it.          *)
Definition card (a:U) : U := inf (fun b => Ordinal b /\ a :~: b).

(* The class of all cardinal numbers.                                           *)
Definition Cardinal : Class := fun b => exists a, b = card a.

(* The cardinal of a set is an ordinal.                                         *)
Proposition IsOrdinal : forall (a:U), Ordinal (card a).
Proof.
  intros a. apply SOI.IsOrdinal.
Qed.

(* The cardinal of a set is a lower bound of all ordinals equivalent to it.     *)
Proposition IsLowerBound : forall (a b:U),
  Ordinal b       ->
  a :~: b         ->
  card a :<=: b.
Proof.
  intros a b H1 H2. apply SOI.IsLowerBound.
  - intros c H3. apply H3.
  - split; assumption.
Qed.

(* The cardinal of a set is the largest such lower bound.                       *)
Proposition IsLargest : forall (a b:U),
  Choice                                        ->
  Ordinal b                                     ->
  (forall c, Ordinal c -> a :~: c -> b :<=: c)  ->
  b :<=: card a.
Proof.
  intros a b AC H1 H2.
  apply SOI.IsLargest.
  - intros c H3. apply H3.
  - assert (exists c, Ordinal c /\ a :~: c) as H3. {
      apply Equiv.HasOrdinal. assumption. }
    destruct H3 as [c H3]. apply CEM.HasElem. exists c. assumption.
  - intros c [H3 H4]. apply H2; assumption.
Qed.

(* When a set has no equivalent ordinal, its cardinal is 0.                     *)
Proposition WhenNoOrdinal : forall (a:U),
  ~ (exists b, Ordinal b /\ a :~: b) -> card a = :0:.
Proof.
  intros a H1. unfold card. apply SOI.IsZero. intros b. split; intros H2.
  - exfalso. destruct H2 as [H2 H3]. apply H1. exists b. assumption.
  - contradiction.
Qed.

(* If a set is equivalent to an ordinal, then it is equivalent to its cardinal. *)
Proposition IsEquivGen : forall (a:U),
  (exists b, Ordinal b /\ a :~: b) -> a :~: card a.
Proof.
  intros a K1.
  remember (fun b => Ordinal b /\ a :~: b) as A eqn:H1.
  assert (A :<=: Ordinal) as H2. { rewrite H1. intros b H2. apply H2. }
  assert (A :<>: :0:) as H3. { apply CEM.HasElem. assumption. }
  assert (A (card a)) as H4. {
    unfold card. rewrite <- H1. apply SOI.IsIn; assumption. }
  rewrite H1 in H4. apply H4.
Qed.

(* Assuming choice, every set is equivalent to its cardinal.                    *)
Proposition IsEquivChoice : forall (a:U), Choice -> a :~: card a.
Proof.
  intros a AC. apply IsEquivGen, HasOrdinal. assumption.
Qed.

(* Every ordinal is equivalent to its cardinal.                                 *)
Proposition IsEquivOrd : forall (a:U), Ordinal a -> a :~: card a.
Proof.
  intros a H1.
  apply IsEquivGen. exists a. split. 1: assumption. apply Equiv.Refl.
Qed.

(* A set with non-empty cardinal is equivalent to its cardinal.                 *)
Proposition IsEquivNotZero : forall (a:U),
  card a <> :0: -> a :~: card a.
Proof.
  intros a H1.
  apply IsEquivGen. apply Classic.DoubleNegation. intros H2.
  apply H1. apply SOI.IsZero. intros x. split; intros H3. 2: contradiction.
  exfalso. apply H2. exists x. apply H3.
Qed.

Proposition Charac : forall (a:U),
  Cardinal a  <-> Ordinal a /\
    forall b, Ordinal b -> a :~: b -> a :<=: b.
Proof.
  intros a. split; intros H1.
  - destruct H1 as [b H1].
    assert (Ordinal a) as H2. { subst. apply IsOrdinal. }
    split. 1: assumption. intros c H3 H4.
    assert (a = :0: \/ a <> :0:) as [H5|H5]. { apply LawExcludedMiddle. }
    + rewrite H5. apply Core.IsIncl. assumption.
    + assert (b :~: card b) as H6. {
        apply IsEquivNotZero. rewrite <- H1. assumption. }
      assert (b :~: c) as H7. {
        apply Equiv.Tran with (card b). 1: assumption.
        rewrite <- H1. assumption. }
      rewrite H1. apply IsLowerBound; assumption.
  - destruct H1 as [H1 H2]. exists a. apply Incl.Double. split.
    + apply H2.
      * apply IsOrdinal.
      * apply IsEquivOrd. assumption.
    + apply IsLowerBound. 1: assumption. apply Equiv.Refl.
Qed.

(* No ordinal strictly below the cardinal of a is equivalent to a.              *)
Proposition IsNotEquiv : forall (a b:U), Ordinal b ->
  b :< card a -> a :<>: b.
Proof.
  intros a b H1 H2 H3.
  assert (card a :<=: b) as H4. { apply IsLowerBound; assumption. }
  assert (b :< b) as H5. { apply H4. assumption. }
  revert H5. apply Foundation.NoLoop1.
Qed.

(* For any ordinal a, its cardinal is a subset of a.                            *)
Proposition IsIncl : forall (a:U), Ordinal a -> card a :<=: a.
Proof.
  intros a H1. apply IsLowerBound. 1: assumption. apply Equiv.Refl.
Qed.

(* Every cardinal is an ordinal.                                                *)
Proposition CardIsOrd : Cardinal :<=: Ordinal.
Proof.
  intros b [a H1]. subst. apply IsOrdinal.
Qed.

(* A set is a cardinal iff it equals its own cardinal.                          *)
Proposition WhenCardinal : forall (a:U), Cardinal a <-> a = card a.
Proof.
  intros a. split; intros H1.
  - destruct H1 as [b H1].
    assert (Ordinal a) as G1. { rewrite H1. apply IsOrdinal. }
    assert (Ordinal (card a)) as G2. { apply IsOrdinal. }
    apply Incl.Double. split.
    + assert (a = :0: \/ :0: :< a) as H2. { apply SOC.ZeroOrElem. assumption. }
      destruct H2 as [H2|H2].
      * rewrite H2. apply SOC.IsIncl. rewrite <- H2. assumption.
      * remember (card a) as c eqn:H3. rewrite H1, H3.
        apply IsLowerBound. 1: apply IsOrdinal.
        apply Equiv.Tran with a.
        { rewrite H1. apply IsEquivNotZero. rewrite <- H1.
          apply Empty.HasElem. exists :0:. assumption. }
        { apply IsEquivOrd. assumption. }
    + apply IsIncl. assumption.
  - exists a. assumption.
Qed.

(* Two equivalent sets have the same cardinal.                                  *)
Proposition WhenEquiv : forall (a b:U),
  a :~: b -> card a = card b.
Proof.
  intros a b H1.
  assert (
    (exists c, Ordinal c /\ a :~: c) \/
   ~(exists c, Ordinal c /\ a :~: c)) as [H2|H2]. { apply LawExcludedMiddle. }
  - assert (exists c, Ordinal c /\ b :~: c) as H3. {
      destruct H2 as [c [H2 H3]]. exists c. split. 1: assumption.
      apply Equiv.Tran with a. 2: assumption. apply Equiv.Sym. assumption. }
    assert (a :~: card a) as H4. { apply IsEquivGen. assumption. }
    assert (b :~: card b) as H5. { apply IsEquivGen. assumption. }
    assert (card a :<=: card b) as H7. {
      apply IsLowerBound.
      - apply IsOrdinal.
      - apply Equiv.Tran with b; assumption. }
    assert (card b :<=: card a) as H8. {
      apply IsLowerBound.
      - apply IsOrdinal.
      - apply Equiv.Tran with a. 2: assumption. apply Equiv.Sym. assumption. }
    apply Incl.Double. split; assumption.
  - assert (~ exists c, Ordinal c /\ b :~: c) as H3. {
      intros H3. destruct H3 as [c [H3 H4]]. apply H2.
      exists c. split. 1: assumption. apply Equiv.Tran with b; assumption. }
    assert (card a = :0:) as H4. { apply WhenNoOrdinal. assumption. }
    assert (card b = :0:) as H5. { apply WhenNoOrdinal. assumption. }
    rewrite H4, H5. reflexivity.
Qed.

(* Assuming choice, two sets are equivalent iff they have the same cardinal.    *)
Proposition EquivCharac : Choice -> forall (a b:U),
  a :~: b <-> card a = card b.
Proof.
  intros AC a b. split; intros H1.
  - apply WhenEquiv. assumption.
  - apply Equiv.Tran with (card a).
    + apply IsEquivChoice. assumption.
    + rewrite H1. apply Equiv.Sym, IsEquivChoice. assumption.
Qed.

(* The cardinal of a cardinal is itself.                                        *)
Proposition Idem : forall (a:U), card (card a) = card a.
Proof.
  intros a. symmetry. apply WhenCardinal. exists a. reflexivity.
Qed.

(* Assuming choice, inclusion implies inequality of cardinals.                  *)
Proposition InclCompat : forall (a b:U), Choice ->
  a :<=: b -> card a :<=: card b.
Proof.
  intros a b AC H1.
  assert (b :~: card b) as H2. { apply IsEquivChoice. assumption. }
  destruct H2 as [f H2].
  assert (exists x, x :<=: card b /\ a :~: x) as H3. {
    exists f:[a]:.
    assert (f:[a]: :<=: card b) as H3. {
      intros y H3.
      apply (Bij.ImageCharac f b (card b)) in H3. 2: assumption.
      destruct H3 as [x [H3 [H4 H5]]].
      apply (Bij.RangeCharac f b (card b)). 1: assumption.
      exists x. split; assumption. }
    assert (a :~: f:[a]:) as H4. {
      exists (f:|:a). apply (Bij.Restrict f b (card b)); assumption. }
    split; assumption. }
  destruct H3 as [x [H3 H4]].
  assert (exists c, Ordinal c /\ c :<=: card b /\ x :~: c) as H5. {
    apply Equiv.OrdinalSubset. 2: assumption. apply IsOrdinal. }
  destruct H5 as [c [H5 [H6 H7]]].
  assert (card a = card x) as H8. { apply EquivCharac; assumption. }
  assert (card x = card c) as H9. { apply EquivCharac; assumption. }
  assert (card c :<=: c) as H10. { apply IsIncl. assumption. }
  rewrite H8, H9. apply Incl.Tran with c; assumption.
Qed.

(* Assuming choice, the Cantor-Schroeder-Bernstein theorem holds.               *)
Proposition CantorShroderBernsteinChoice : forall (a b c d:U),
  Choice    ->
  a :~: c   ->
  b :~: d   ->
  c :<=: b  ->
  d :<=: a  ->
  a :~: b.
Proof.
  intros a b c d AC H1 H2 H3 H4.
  assert (card a = card c) as H5. { apply EquivCharac; assumption. }
  assert (card b = card d) as H6. { apply EquivCharac; assumption. }
  assert (card c :<=: card b) as H7. { apply InclCompat; assumption. }
  assert (card d :<=: card a) as H8. { apply InclCompat; assumption. }
  apply EquivCharac. assumption. apply Incl.Double. split.
  - rewrite H5. assumption.
  - rewrite H6. assumption.
Qed.

(* Assuming choice, the cardinal of a is strictly smaller than card(P(a)).      *)
Proposition Cantor : forall (a:U), Choice ->
  card a :< card :P(a).
Proof.
  intros a AC.
  assert (exists b, Ordinal b /\ a :~: b) as H1. {
    apply HasOrdinal. assumption. }
  destruct H1 as [b [H1 H2]].
  assert (Ordinal (card b)) as G1. { apply IsOrdinal. }
  assert (Ordinal (card :P(b))) as G2. { apply IsOrdinal. }
  assert (card a = card b) as H3. { apply EquivCharac; assumption. }
  assert (card :P(a) = card :P(b)) as H4. {
    apply EquivCharac, Equiv.PowerCompat; assumption. }
  assert (card b :< card :P(b)) as H5. {
    assert (b :<=: :P(b)) as H5. {
      intros c H5.
      assert (Ordinal c) as K1. { apply SOC.IsOrdinal with b; assumption. }
      apply Power.Charac. intros d H6.
      assert (Ordinal d) as K2. { apply SOC.IsOrdinal with c; assumption. }
      apply SOC.ElemElemTran with c; assumption. }
  assert (card b :<=: card :P(b)) as H6. { apply InclCompat; assumption. }
  assert (card b = card :P(b) \/ card b :< card :P(b)) as H7. {
    apply SOC.EqualOrElem; assumption. }
  destruct H7 as [H7|H7]. 2:assumption. exfalso.
  assert (b :~: :P(b)) as H8. { apply EquivCharac; assumption. }
  apply Equiv.Cantor with b. assumption. }
  rewrite H3, H4. assumption.
Qed.

(* The cardinal of a natural number is itself.                                  *)
Proposition WhenNat : forall (n:U), n :< :N ->
  card n = n.
Proof.
  (* Proof by Claude. *)
  intros n H1.
  (* n is an ordinal (naturals are), so n ~ card n; card n ~ n by symmetry;     *)
  (* card n is an ordinal equipotent to n, so it equals n.                      *)
  apply EqualOrdNat. 2: assumption.
  - apply IsOrdinal.
  - apply Equiv.Sym, IsEquivOrd, Omega.HasOrdinals. assumption.
Qed.

(* Every natural number is a cardinal number.                                   *)
Proposition NatIsCardinal : forall (n:U),
  n :< :N -> Cardinal n.
Proof.
  intros n H1. exists n. symmetry. apply WhenNat. assumption.
Qed.

(* N is a cardinal number.                                                      *)
Proposition HasOmega : Cardinal :N.
Proof.
  (* Proof by Claude.                                                           *)
  exists :N.
  assert (Ordinal :N) as H1. { apply Omega.IsOrdinal. }
  assert (Ordinal (card :N)) as H2. { apply IsOrdinal. }
  (* By ordinal trichotomy, card(N) < N or N <= card(N).                        *)
  assert (card :N :< :N \/ :N :<=: card :N) as H3. {
    apply SOC.ElemOrIncl; assumption. }
  destruct H3 as [H3|H3].
  - (* card(N) < N: N ~ card(N) as N is an ordinal, and any ordinal in          *)
    (* bijection with a natural number equals it, giving N = card(N).           *)
    assert (:N :~: card :N) as H4. { apply IsEquivOrd. assumption. }
    apply EqualOrdNat; assumption.
  - (* N <= card(N): card(N) <= N as N is an ordinal, so N = card(N).           *)
    apply Incl.Double. split. 1: assumption. apply IsIncl. assumption.
Qed.

