Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Onto.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Fun.From2.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Specify.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CEM := ZF.Class.Empty.
Module CRL := ZF.Class.Relation.Functional.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.
Module SOO := ZF.Set.Ordinal.Onto.
Module SRF := ZF.Set.Relation.Fun.
Module SFL := ZF.Set.Relation.Functional.
Module SRD := ZF.Set.Relation.Domain.
Module SRN := ZF.Set.Relation.Function.
Module SRO := ZF.Set.Relation.Onto.
Module SRR := ZF.Set.Relation.Range.
Module SRS := ZF.Set.Relation.Restrict.

(* The cardinal of a set is the smallest ordinal in bijection with it.          *)
Definition card (a:U) : U := inf (fun b => Ordinal b /\ a :~: b).

(* The class of all cardinal numbers.                                           *)
Definition Cardinal : Class := fun b => exists a, b = card a.

(* The cardinal of a set is an ordinal.                                         *)
Proposition IsOrdinal : forall (a:U), Ordinal (card a).
Proof.
  intros a. apply SOI.IsOrdinal.
Qed.

(* The cardinal of a set is a lower bound of all ordinals equipotent to it.     *)
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
      apply Equiv.IsWellOrderable. assumption. }
    destruct H3 as [c H3]. apply CEM.HasElem. exists c. assumption.
  - intros c [H3 H4]. apply H2; assumption.
Qed.

(* When a set is not well-orderable, its cardinal is 0.                         *)
Proposition WhenNotWellOrderable : forall (a:U),
  ~ WellOrderable a -> card a = :0:.
Proof.
  intros a H1. unfold card. apply SOI.IsZero. intros b. split; intros H2.
  - exfalso. destruct H2 as [H2 H3]. apply H1. exists b. assumption.
  - contradiction.
Qed.

(* A well-orderable set is equipotent to its cardinal.                          *)
Proposition IsEquivGen : forall (a:U), WellOrderable a ->
  a :~: card a.
Proof.
  intros a K1. unfold WellOrderable in K1.
  remember (fun b => Ordinal b /\ a :~: b) as A eqn:H1.
  assert (A :<=: Ordinal) as H2. { rewrite H1. intros b H2. apply H2. }
  assert (A :<>: :0:) as H3. { apply CEM.HasElem. assumption. }
  assert (A (card a)) as H4. {
    unfold card. rewrite <- H1. apply SOI.IsIn; assumption. }
  rewrite H1 in H4. apply H4.
Qed.

(* Assuming choice, every set is equipotent to its cardinal.                    *)
Proposition IsEquivChoice : forall (a:U), Choice ->
  a :~: card a.
Proof.
  intros a AC. apply IsEquivGen, IsWellOrderable. assumption.
Qed.

(* Every ordinal is equipotent to its cardinal.                                 *)
Proposition IsEquivOrd : forall (a:U), Ordinal a ->
  a :~: card a.
Proof.
  intros a H1.
  apply IsEquivGen. exists a. split. 1: assumption. apply Equiv.Refl.
Qed.

(* A set with non-empty cardinal is equipotent to its cardinal.                 *)
Proposition IsEquivNotZero : forall (a:U), card a <> :0: ->
  a :~: card a.
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
    + rewrite H5. apply Empty.IsIncl.
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

(* No ordinal strictly below the cardinal of a is equipotent to a.              *)
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
      * rewrite H2. apply Empty.IsIncl.
      * remember (card a) as c eqn:H3. rewrite H1, H3.
        apply IsLowerBound. 1: apply IsOrdinal.
        apply Equiv.Tran with a.
        { rewrite H1. apply IsEquivNotZero. rewrite <- H1.
          apply Empty.HasElem. exists :0:. assumption. }
        { apply IsEquivOrd. assumption. }
    + apply IsIncl. assumption.
  - exists a. assumption.
Qed.

(* Two equipotent sets have the same cardinal.                                  *)
Proposition WhenEquiv : forall (a b:U),
  a :~: b -> card a = card b.
Proof.
  intros a b H1.
  assert (WellOrderable a \/ ~ WellOrderable a) as [H2|H2]. {
    apply LawExcludedMiddle. }
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
    assert (card a = :0:) as H4. { apply WhenNotWellOrderable. assumption. }
    assert (card b = :0:) as H5. { apply WhenNotWellOrderable. assumption. }
    rewrite H4, H5. reflexivity.
Qed.

(* Assuming choice, two sets are equipotent iff they have the same cardinal.    *)
Proposition EquivCharac : forall (a b:U),
  Choice -> a :~: b <-> card a = card b.
Proof.
  intros a b AC. split; intros H1.
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

(* The cardinal of a product is unchanged when the factors are exchanged.       *)
Proposition ProdComm : forall (a b:U),
  card (a :x: b) = card (b :x: a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b.
  (* Exchanging the factors gives a bijection between the two products.         *)
  apply WhenEquiv. apply Equiv.ProdComm.
Qed.

Proposition InclCompatGen : forall (a b:U), WellOrderable b ->
  a :<=: b -> card a :<=: card b.
Proof.
  intros a b G1 H1.
  assert (b :~: card b) as H2. { apply IsEquivGen. assumption. }
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
  assert (card a = card x) as H8. { apply WhenEquiv. assumption. }
  assert (card x = card c) as H9. { apply WhenEquiv. assumption. }
  assert (card c :<=: c) as H10. { apply IsIncl. assumption. }
  rewrite H8, H9. apply Incl.Tran with c; assumption.
Qed.

(* Assuming choice, inclusion implies inequality of cardinals.                  *)
Proposition InclCompat : forall (a b:U), Choice ->
  a :<=: b -> card a :<=: card b.
Proof.
  intros a b AC. apply InclCompatGen, Equiv.IsWellOrderable. assumption.
Qed.

(* Any set whose cardinal is bounded by card(a) is equipotent to a subset of a. *)
Proposition HasSubsetOfSize : forall (a c:U), Choice ->
  c :<=: card a -> exists b, b :<=: a /\ b :~: c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a c AC H1.
  (* Choose a bijection from card(a) onto a, and take the image of c.           *)
  assert (a :~: card a) as H2. { apply IsEquivChoice. assumption. }
  apply Equiv.Sym in H2. destruct H2 as [f H2].
  exists f:[c]:. split.
  - (* Since c is contained in card(a), its image is contained in a.            *)
    intros y H3. apply (Bij.ImageCharac f (card a) a c) in H3. 2: assumption.
    destruct H3 as [x [H3 [H4 H5]]]. rewrite <- H5.
    apply Bij.IsInRange with (card a); assumption.
  - (* Restricting the bijection to c bijects c onto its image.                 *)
    apply Equiv.Sym. exists (f:|:c).
    apply (Bij.Restrict f (card a) a c); assumption.
Qed.

Proposition IsInclSucc : forall (a:U),
  card a :<=: card (succ a).
Proof.
  intros a.
  assert (WellOrderable a \/ ~ WellOrderable a) as [H1|H1]. {
    apply LawExcludedMiddle. }
  - assert (WellOrderable (succ a)) as H2. {
      apply Equiv.WellOrderableSucc. assumption. }
    apply InclCompatGen. 1: assumption. apply Succ.IsIncl.
  - assert (card a = :0:) as H2. { apply WhenNotWellOrderable. assumption. }
    assert (Ordinal (card (succ a))) as H3. { apply IsOrdinal. }
    rewrite H2. apply Empty.IsIncl.
Qed.

Proposition IsInclSucc' : forall (a:U),
  card (succ a) :<=: succ (card a).
Proof.
  intros a.
  assert (WellOrderable a \/ ~ WellOrderable a) as [H1|H1]. {
    apply LawExcludedMiddle. }
  - assert (Ordinal (succ (card a))) as H2. { apply Succ.IsOrdinal, IsOrdinal. }
    assert (a :~: card a) as H3. { apply IsEquivGen. assumption. }
    assert (succ a :~: succ (card a)) as H4. { apply SuccCompat. assumption. }
    apply IsLowerBound; assumption.
  - assert (~ WellOrderable (succ a)) as H2. {
      intros H2. apply H1. apply Equiv.WellOrderableSuccRev. assumption. }
    assert (card (succ a) = :0:) as H3. { apply WhenNotWellOrderable. assumption. }
    rewrite H3. apply Empty.IsIncl.
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
    apply IsWellOrderable. assumption. }
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
  (* Proof by Claude + sonnet 4.6                                               *)
  intros n H1.
  (* n is an ordinal (naturals are), so n ~ card n; card n ~ n by symmetry;     *)
  (* card n is an ordinal equipotent to n, so it equals n.                      *)
  apply EqualOrdNat. 2: assumption.
  - apply IsOrdinal.
  - apply Equiv.Sym, IsEquivOrd, Omega.HasOrdinals. assumption.
Qed.

(* A set with non-empty cardinal is not empty.                                  *)
Proposition NotZero : forall (a:U),
  card a <> :0: -> a <> :0:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1 H2.
  (* The empty set has cardinal zero, contrary to the hypothesis.               *)
  apply H1. rewrite H2. apply WhenNat. apply Omega.HasZero.
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
  (* Proof by Claude + sonnet 4.6                                               *)
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

(* If b is not empty, then card(a) is bounded by card(a x b).                   *)
Proposition IsInclProdR : forall (a b:U), Choice ->
  b <> :0: -> card a :<=: card (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  apply Empty.HasElem in H1. destruct H1 as [y H1].
  remember (From.from a (fun x => :(x,y):)) as f eqn:H2.
  (* Fixing y in b embeds a into a x b by sending x to (x,y).                   *)
  assert (Inj f a (a :x: b)) as H3. {
    rewrite H2. apply From.IsInj.
    - intros x H3. apply Prod.Charac2. split; assumption.
    - intros x z H3 H4 H5.
      apply OrdPair.Equal in H5. destruct H5 as [H5 _]. assumption. }
  (* Hence a is bijective with its image, which lies inside a x b.              *)
  assert (a :~: f:[a]:) as H4. { exists f. apply Bij.FromInj with (a :x: b).
    assumption. }
  assert (card a = card f:[a]:) as H5. { apply WhenEquiv. assumption. }
  rewrite H5. apply InclCompat. 1: assumption.
  rewrite (Inj.ImageOfDomain f a (a :x: b)). 2: assumption. apply H3.
Qed.

(* If a is not empty, then card(b) is bounded by card(a x b).                   *)
Proposition IsInclProdL : forall (a b:U), Choice ->
  a <> :0: -> card b :<=: card (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Exchange the product factors and use the right-factor version.             *)
  rewrite ProdComm. apply IsInclProdR; assumption.
Qed.

(* If a and b are well-orderable, card(a) <= card(b) gives an injection a -> b. *)
Proposition HasInjGen : forall (a b:U), WellOrderable a -> WellOrderable b ->
  card a :<=: card b -> exists f, Inj f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2 H3.
  (* Choose bijections a -> card(a) and card(b) -> b.                           *)
  assert (a :~: card a) as H4. { apply IsEquivGen. assumption. }
  assert (card b :~: b) as H5. { apply Equiv.Sym, IsEquivGen. assumption. }
  destruct H4 as [f H4]. destruct H5 as [g H5].
  (* The first bijection is an injection into card(a).                          *)
  assert (Inj f a (card a)) as H6. { apply Bij.IsInj. assumption. }
  (* Restrict the second injection to the smaller ordinal card(a).              *)
  assert (Inj (g:|:card a) (card a) b) as H7. {
    apply Inj.Restrict with (card b). 2: assumption.
    apply Bij.IsInj. assumption. }
  (* Composing the two injections embeds a into b.                              *)
  exists ((g:|:card a) :.: f). apply Inj.Compose with (card a); assumption.
Qed.

(* Assuming choice, card(a) <= card(b) gives an injection from a into b.        *)
Proposition HasInj : forall (a b:U), Choice ->
  card a :<=: card b -> exists f, Inj f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Choice supplies the well-orderability assumptions needed by HasInjGen.     *)
  assert (WellOrderable a) as H2. { apply Equiv.IsWellOrderable. assumption. }
  assert (WellOrderable b) as H3. { apply Equiv.IsWellOrderable. assumption. }
  apply HasInjGen; assumption.
Qed.

(* If a and b are well-orderable, card(b) <= card(a) gives a surjection a -> b. *)
Proposition HasOntoGen : forall (a b:U), WellOrderable a -> WellOrderable b ->
  b <> :0: -> card b :<=: card a -> exists f, Onto f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2 H3 H4.
  (* Move to cardinals, retract the larger ordinal onto the smaller one, and    *)
  (* then move back to b.                                                       *)
  assert (a :~: card a) as H5. { apply IsEquivGen. assumption. }
  assert (card b :~: b) as H6. { apply Equiv.Sym, IsEquivGen. assumption. }
  destruct H5 as [e H5]. destruct H6 as [h H6].
  assert (Onto e a (card a)) as H7. { apply Bij.IsOnto. assumption. }
  assert (Onto h (card b) b) as H8. { apply Bij.IsOnto. assumption. }
  assert (card b <> :0:) as H9. {
    intros H9. apply H3. apply SCE.WhenZero.
    rewrite <- H9. apply Equiv.Sym. exists h. assumption. }
  assert (exists r, Onto r (card a) (card b)) as H10. {
    apply SOO.WhenIncl.
    - apply IsOrdinal.
    - apply IsOrdinal.
    - assumption.
    - assumption. }
  destruct H10 as [r H10].
  assert (Onto (r :.: e) a (card b)) as H11. {
    apply SRO.Compose with (card a); assumption. }
  exists (h :.: (r :.: e)). apply SRO.Compose with (card b); assumption.
Qed.

(* Assuming choice, card(b) <= card(a) gives a surjection from a onto b.        *)
Proposition HasOnto : forall (a b:U), Choice ->
  b <> :0: -> card b :<=: card a -> exists f, Onto f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1 H2.
  (* Choice supplies the well-orderability assumptions needed by HasOntoGen.    *)
  assert (WellOrderable a) as H3. { apply Equiv.IsWellOrderable. assumption. }
  assert (WellOrderable b) as H4. { apply Equiv.IsWellOrderable. assumption. }
  apply HasOntoGen; assumption.
Qed.

(* An injection into a well-orderable set gives an inequality of cardinals.     *)
Proposition WhenInjGen : forall (a b f:U), WellOrderable b ->
  Inj f a b -> card a :<=: card b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1 H2.
  (* The domain is equipotent to its image, and that image is contained in b.   *)
  assert (a :~: f:[a]:) as H3. { exists f. apply Bij.FromInj with b. assumption. }
  assert (card a = card f:[a]:) as H4. { apply WhenEquiv. assumption. }
  rewrite H4. apply InclCompatGen. 1: assumption.
  rewrite (Inj.ImageOfDomain f a b). 2: assumption. apply H2.
Qed.

(* Assuming choice, an injection gives an inequality of cardinals.              *)
Proposition WhenInj : forall (a b f:U), Choice ->
  Inj f a b -> card a :<=: card b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f AC H1.
  (* Choice makes the codomain well-orderable, so the general form applies.     *)
  apply WhenInjGen with f. 2: assumption.
  apply Equiv.IsWellOrderable. assumption.
Qed.

(* A surjection from a well-orderable set gives an inequality of cardinals.     *)
Proposition WhenOntoGen : forall (f a b:U), WellOrderable a ->
  Onto f a b -> card b :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1 H2.
  (* Reindex the surjection by a bijection from card(a) onto a.                 *)
  assert (card a :~: a) as H3. { apply Equiv.Sym, IsEquivGen. assumption. }
  destruct H3 as [e H3].
  assert (Onto e (card a) a) as H4. { apply Bij.IsOnto. assumption. }
  assert (Onto (f :.: e) (card a) b) as H5. {
    apply SRO.Compose with a; assumption. }
  (* The ordinal-domain surjection has a bijective restriction.                 *)
  assert (exists d, d :<=: card a /\ Bij ((f :.: e) :|: d) d b) as H6. {
    apply SOO.HasRestrictBij. 1: apply IsOrdinal. assumption. }
  destruct H6 as [d [H6 H7]].
  (* The codomain has the cardinal of a subset of card(a).                      *)
  assert (card b = card d) as H8. {
    apply WhenEquiv. apply Equiv.Sym. exists ((f :.: e) :|: d). assumption. }
  rewrite H8. rewrite <- (Idem a). apply InclCompatGen. 2: assumption.
  exists (card a). split. 1: apply IsOrdinal. apply Equiv.Refl.
Qed.

(* Assuming choice, a surjection gives an inequality of cardinals.              *)
Proposition WhenOnto : forall (f a b:U), Choice ->
  Onto f a b -> card b :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b AC H1.
  (* Choice makes the domain well-orderable, so the general form applies.       *)
  apply WhenOntoGen with f. 2: assumption.
  apply Equiv.IsWellOrderable. assumption.
Qed.

(* Cardinal product is monotone in its right argument.                          *)
Proposition InclCompatProdR : forall (a b c:U), Choice ->
  card b :<=: card c -> card (a :x: b) :<=: card (a :x: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* From card(b) <= card(c), choose an injection f:b -> c.                     *)
  assert (exists f, Inj f b c) as H2. { apply HasInj; assumption. }
  destruct H2 as [f H2].
  remember (From2.from2 a b (fun x y => :(x,f!y):)) as g eqn:H3.
  (* Send (x,y) to (x,f(y)); this preserves the left coordinate and injects the *)
  (* right coordinate through f.                                                *)
  assert (Inj g (a :x: b) (a :x: c)) as H4. {
    rewrite H3. apply From2.IsInj.
    - intros x y H4 H5. apply Prod.Charac2. split. 1: assumption.
      apply Inj.IsInRange with b; assumption.
    - intros x y x' y' H4 H5 H6 H7 H8.
      apply OrdPair.Equal in H8. destruct H8 as [H8 H9]. subst x'.
      assert (y = y') as H10. {
        apply Inj.EvalInjective with f b c; assumption. }
      subst y'. reflexivity. }
  (* The product injection gives the desired cardinal inequality.               *)
  apply WhenInj with g; assumption.
Qed.

(* Cardinal product is monotone in its left argument.                           *)
Proposition InclCompatProdL : forall (a b c:U), Choice ->
  card a :<=: card b -> card (a :x: c) :<=: card (b :x: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* Exchange the product factors and use monotonicity in the right argument.   *)
  rewrite (ProdComm a c), (ProdComm b c). apply InclCompatProdR; assumption.
Qed.

(* Cardinal product is monotone in both arguments.                              *)
Proposition InclCompatProd : forall (a b c d:U), Choice ->
  card a :<=: card c -> card b :<=: card d ->
  card (a :x: b) :<=: card (c :x: d).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c d AC H1 H2.
  (* First enlarge the left factor, then enlarge the right factor.              *)
  apply Incl.Tran with (card (c :x: b)).
  - apply InclCompatProdL; assumption.
  - apply InclCompatProdR; assumption.
Qed.

(* The cardinal of the image of a set under a functional class is bounded.      *)
Proposition Image : forall (F:Class) (a:U), Choice ->
  CRL.Functional F -> card F:[a]: :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros F a AC H1.
  (* The restriction of F to a is a surjection from its domain onto its range.  *)
  assert (Onto (F:|:a) (SRD.domain (F:|:a)) (SRR.range (F:|:a))) as H2. {
    split. 2: reflexivity. split. 2: reflexivity.
    apply RestrictOfClass.IsFunction. assumption. }
  (* The range of the restriction is exactly the direct image of a under F.     *)
  assert (SRR.range (F:|:a) = F:[a]:) as H3. {
    apply RestrictOfClass.RangeOf. assumption. }
  (* The domain of the restriction is contained in a.                           *)
  assert (SRD.domain (F:|:a) :<=: a) as H4. {
    apply RestrictOfClass.DomainIsIncl. assumption. }
  (* A surjection bounds the cardinal of its range by the cardinal of its       *)
  (* domain, and the latter domain is bounded by a.                             *)
  assert (card (SRR.range (F:|:a)) :<=: card (SRD.domain (F:|:a))) as H5. {
    apply WhenOnto with (F:|:a); assumption. }
  assert (card (SRD.domain (F:|:a)) :<=: card a) as H6. {
    apply InclCompat; assumption. }
  rewrite <- H3. apply Incl.Tran with (card (SRD.domain (F:|:a))); assumption.
Qed.

