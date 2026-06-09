Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Induction.
Require Import ZF.Class.Ordinal.Order.MaxLex.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Cardinal.WellOrderable.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Onto.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Fun.IfThenElse.
Require Import ZF.Set.Relation.Id.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Map.Sum.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Sum.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CEM := ZF.Class.Empty.
Module CRD := ZF.Class.Relation.Domain.
Module CRL := ZF.Class.Relation.Functional.
Module CRO := ZF.Class.Relation.OneToOne.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SCW := ZF.Set.Cardinal.WellOrderable.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.
Module SOO := ZF.Set.Ordinal.Onto.
Module SFI := ZF.Set.Relation.Fun.IfThenElse.
Module SRD := ZF.Set.Relation.Domain.
Module SRR := ZF.Set.Relation.Range.
Module SRO := ZF.Set.Relation.Onto.
Module SMS := ZF.Set.Relation.Map.Sum.

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
(* When a set is not well-orderable, its cardinal is 0.                         *)
Proposition WhenNotWellOrderable : forall (a:U),
  ~ WellOrderable a -> card a = :0:.
Proof.
  intros a H1. unfold card. apply SOI.IsZero. intros b. split; intros H2.
  - exfalso. destruct H2 as [H2 H3]. apply H1. exists b. assumption.
  - contradiction.
Qed.

(* A well-orderable set is equipotent to its cardinal.                          *)
Proposition IsEquiv : forall (a:U), WellOrderable a ->
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
(* Every ordinal is equipotent to its cardinal.                                 *)
Proposition IsEquivOrd : forall (a:U), Ordinal a ->
  a :~: card a.
Proof.
  intros a H1.
  apply IsEquiv. exists a. split. 1: assumption. apply Equiv.Refl.
Qed.

(* A set with non-empty cardinal is equipotent to its cardinal.                 *)
Proposition IsEquivNotZero : forall (a:U), card a <> :0: ->
  a :~: card a.
Proof.
  intros a H1.
  apply IsEquiv. apply Classic.DoubleNegation. intros H2.
  apply H1. apply SOI.IsZero. intros x. split; intros H3. 2: contradiction.
  exfalso. apply H2. exists x. apply H3.
Qed.

(* A set with non-empty cardinal is well-orderable.                             *)
Proposition WellOrderableNotZero : forall (a:U), card a <> :0: ->
  WellOrderable a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1.
  (* Its cardinal is an ordinal representative equipotent to the set.           *)
  exists (card a). split. 1: apply IsOrdinal. apply IsEquivNotZero. assumption.
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
    assert (a :~: card a) as H4. { apply IsEquiv. assumption. }
    assert (b :~: card b) as H5. { apply IsEquiv. assumption. }
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

(* Well-orderable sets are equipotent iff they have the same cardinal.          *)
Proposition EquivCharac : forall (a b:U),
  WellOrderable a -> WellOrderable b -> a :~: b <-> card a = card b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2. split; intros H3.
  - (* Equipotent sets always have the same cardinal.                           *)
    apply WhenEquiv. assumption.
  - (* The two sets are both equipotent to their common cardinal.               *)
    apply Equiv.Tran with (card a).
    + apply IsEquiv. assumption.
    + rewrite H3. apply Equiv.Sym, IsEquiv. assumption.
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

Proposition InclCompat : forall (a b:U), WellOrderable b ->
  a :<=: b -> card a :<=: card b.
Proof.
  intros a b G1 H1.
  assert (b :~: card b) as H2. { apply IsEquiv. assumption. }
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

(* An ordinal is below a cardinal iff its cardinal is below that cardinal.      *)
Proposition CardLess : forall (a b:U),
  Ordinal a  ->
  Cardinal b ->
  card a :< b <-> a :< b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2.
  (* A cardinal is an ordinal, so a and b are comparable by membership.         *)
  assert (Ordinal b) as H3. { apply CardIsOrd. assumption. }
  split; intros H4.
  - assert (a :< b \/ b :<=: a) as H5. { apply SOC.ElemOrIncl; assumption. }
    destruct H5 as [H5|H5]. 1: assumption.
    (* If b were included in a, then the cardinal b would be below card(a).     *)
    assert (WellOrderable a) as H6. { apply SCW.WhenOrdinal. assumption. }
    assert (card b :<=: card a) as H7. { apply InclCompat; assumption. }
    assert (b = card b) as H8. { apply WhenCardinal. assumption. }
    rewrite <- H8 in H7.
    assert (card a :< card a) as H9. { apply H7. assumption. }
    exfalso. revert H9. apply Foundation.NoLoop1.
  - (* Since card(a) is included in a, membership of a in b carries card(a).    *)
    apply SOC.InclElemTran with a; try assumption.
    + apply IsOrdinal.
    + apply IsIncl. assumption.
Qed.
Proposition IsInclSucc : forall (a:U),
  card a :<=: card (succ a).
Proof.
  intros a.
  assert (WellOrderable a \/ ~ WellOrderable a) as [H1|H1]. {
    apply LawExcludedMiddle. }
  - assert (WellOrderable (succ a)) as H2. {
      apply SCW.Succ. assumption. }
    apply InclCompat. 1: assumption. apply Succ.IsIncl.
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
    assert (a :~: card a) as H3. { apply IsEquiv. assumption. }
    assert (succ a :~: succ (card a)) as H4. { apply SuccCompat. assumption. }
    apply IsLowerBound; assumption.
  - assert (~ WellOrderable (succ a)) as H2. {
      intros H2. apply H1. apply SCW.SuccRev. assumption. }
    assert (card (succ a) = :0:) as H3. { apply WhenNotWellOrderable. assumption. }
    rewrite H3. apply Empty.IsIncl.
Qed.

(* An infinite ordinal has the same cardinal as its successor.                  *)
Proposition Succ : forall (a:U), Ordinal a ->
  :N :<=: a -> card a = card (succ a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1 H2.
  (* The ordinal is equipotent to its successor, so their cardinals coincide.   *)
  apply WhenEquiv. apply SCE.Succ; assumption.
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

(* The cardinal of N is N.                                                      *)
Proposition WhenOmega : card :N = :N.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Ordinal :N) as H1. { apply Omega.IsOrdinal. }
  assert (Ordinal (card :N)) as H2. { apply IsOrdinal. }
  (* By ordinal trichotomy, card(N) is either below N or contains N.            *)
  assert (card :N :< :N \/ :N :<=: card :N) as H3. {
    apply SOC.ElemOrIncl; assumption. }
  destruct H3 as [H3|H3].
  - (* If card(N) is a natural number, equipotence forces it to be N itself.    *)
    assert (:N :~: card :N) as H4. { apply IsEquivOrd. assumption. }
    symmetry. apply EqualOrdNat; assumption.
  - (* Otherwise, the two ordinal inclusions give equality.                     *)
    apply Incl.Double. split. 2: assumption. apply IsIncl. assumption.
Qed.

(* N is a cardinal number.                                                      *)
Proposition HasOmega : Cardinal :N.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  exists :N. symmetry. apply WhenOmega.
Qed.

(* A set whose cardinal is greater than one contains two distinct elements.     *)
Proposition HasTwoElems : forall (a:U),
  :1: :< card a -> exists x y, x :< a /\ y :< a /\ x <> y.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1.
  (* Since the cardinal is not zero, a is equipotent to its cardinal.           *)
  assert (card a <> :0:) as H2. {
    intros H2. rewrite H2 in H1. apply Empty.Charac in H1. contradiction. }
  assert (a :~: card a) as H3. { apply IsEquivNotZero. assumption. }
  destruct H3 as [f H3].
  (* Since card(a) is a non-zero ordinal, it contains 0.                        *)
  assert (:0: :< card a) as H4. {
    apply SOC.HasZero. 1: apply IsOrdinal. assumption. }
  assert (:1: :< card a) as H5. { assumption. }
  (* Take their inverse images under the bijection a -> card(a).                *)
  assert (exists x, x :< a /\ f!x = :0:) as H6. {
    apply (Bij.RangeCharac f a (card a) :0:); assumption. }
  assert (exists y, y :< a /\ f!y = :1:) as H7. {
    apply (Bij.RangeCharac f a (card a) :1:); assumption. }
  destruct H6 as [x [H6 H8]]. destruct H7 as [y [H7 H9]].
  exists x, y. split. 1: assumption. split. 1: assumption.
  (* Distinct values in the cardinal have distinct preimages.                   *)
  intros H10. subst y. rewrite H8 in H9.
  apply Natural.ZeroIsNotOne. assumption.
Qed.
(* If a and b are well-orderable, card(a) <= card(b) gives an injection a -> b. *)
Proposition HasInj : forall (a b:U), WellOrderable a -> WellOrderable b ->
  card a :<=: card b -> exists f, Inj f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2 H3.
  (* Choose bijections a -> card(a) and card(b) -> b.                           *)
  assert (a :~: card a) as H4. { apply IsEquiv. assumption. }
  assert (card b :~: b) as H5. { apply Equiv.Sym, IsEquiv. assumption. }
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
(* If a and b are well-orderable, card(b) <= card(a) gives a surjection a -> b. *)
Proposition HasOnto : forall (a b:U), WellOrderable a -> WellOrderable b ->
  b <> :0: -> card b :<=: card a -> exists f, Onto f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2 H3 H4.
  (* Move to cardinals, retract the larger ordinal onto the smaller one, and    *)
  (* then move back to b.                                                       *)
  assert (a :~: card a) as H5. { apply IsEquiv. assumption. }
  assert (card b :~: b) as H6. { apply Equiv.Sym, IsEquiv. assumption. }
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
(* An injection into a well-orderable set gives an inequality of cardinals.     *)
Proposition WhenInj : forall (a b f:U), WellOrderable b ->
  Inj f a b -> card a :<=: card b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1 H2.
  (* The domain is equipotent to its image, and that image is contained in b.   *)
  assert (a :~: f:[a]:) as H3. { exists f. apply Bij.FromInj with b. assumption. }
  assert (card a = card f:[a]:) as H4. { apply WhenEquiv. assumption. }
  rewrite H4. apply InclCompat. 1: assumption.
  rewrite (Inj.ImageOfDomain f a b). 2: assumption. apply H2.
Qed.
(* If a is an ordinal above one, then succ(a) is bounded by a x a.              *)
Proposition SuccSquare : forall (a:U),
  Ordinal a -> :1: :< a -> card (succ a) :<=: card (a :x: a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1 H2.
  (* Both zero and one lie in a, and the square is well-orderable.              *)
  assert (:0: :< a) as H3. {
    apply SOC.ElemElemTran with :1:; try assumption.
    - apply SOC.Zero.
    - apply Natural.OneIsOrdinal.
    - apply Succ.IsIn. }
  assert (WellOrderable a) as H4. { apply SCW.WhenOrdinal. assumption. }
  assert (WellOrderable (a :x: a)) as H5. { apply SCW.Prod; assumption. }
  remember (SFI.ifThenElse (succ a) (fun x => x :< a)
    (fun x => :(:0:,x):) (fun _ => :(:1:,:0:):)) as f eqn:H6.
  (* Both displayed branch values lie in the square a x a.                      *)
  assert (SFI.MapsTo (succ a) (a :x: a) (fun x => x :< a)
    (fun x => :(:0:,x):) (fun _ => :(:1:,:0:):)) as H7. {
    split; intros x H7 H8; apply Prod.Charac2; split; assumption. }
  (* Equal old-branch values have the same second coordinate.                   *)
  assert (forall x y, x :< succ a -> y :< succ a -> x :< a -> y :< a ->
    :(:0:,x): = :(:0:,y): -> x = y) as H8. {
    intros x y H8 H9 H10 H11 H12.
    apply OrdPair.Equal in H12. destruct H12 as [_ H12]. assumption. }
  (* The old branch cannot meet the new-point branch.                           *)
  assert (forall x y, x :< succ a -> y :< succ a -> x :< a -> ~ y :< a ->
    :(:0:,x): = :(:1:,:0:): -> x = y) as H9. {
    intros x y H9 H10 H11 H12 H13.
    exfalso. apply OrdPair.Equal in H13. destruct H13 as [H13 _].
    apply Natural.ZeroIsNotOne. assumption. }
  (* The new-point branch cannot meet the old branch.                           *)
  assert (forall x y, x :< succ a -> y :< succ a -> ~ x :< a -> y :< a ->
    :(:1:,:0:): = :(:0:,y): -> x = y) as H10. {
    intros x y H10 H11 H12 H13 H14.
    exfalso. apply OrdPair.Equal in H14. destruct H14 as [H14 _].
    apply Natural.ZeroIsNotOne. symmetry. assumption. }
  (* The only element of succ(a) outside a is a itself.                         *)
  assert (forall x y, x :< succ a -> y :< succ a -> ~ x :< a -> ~ y :< a ->
    :(:1:,:0:): = :(:1:,:0:): -> x = y) as H11. {
    intros x y H11 H12 H13 H14 H15.
    apply Succ.Charac in H11. destruct H11 as [H11|H11]. 2: contradiction.
    apply Succ.Charac in H12. destruct H12 as [H12|H12]. 2: contradiction.
    subst. reflexivity. }
  (* These branch facts show that the piecewise map is injective.               *)
  assert (SFI.Injective (succ a) (fun x => x :< a)
    (fun x => :(:0:,x):) (fun _ => :(:1:,:0:):)) as H12. {
    repeat split; intros x y K1 K2 K3 K4 K5.
    - apply H8; assumption.
    - apply H9; assumption.
    - apply H10; assumption.
    - apply H11; assumption. }
  assert (Inj f (succ a) (a :x: a)) as H13. {
    rewrite H6. apply SFI.IsInj; assumption. }
  (* An injection into the well-orderable square gives the cardinal bound.      *)
  apply WhenInj with f; assumption.
Qed.
(* A surjection from a well-orderable set gives an inequality of cardinals.     *)
Proposition WhenOnto : forall (f a b:U), WellOrderable a ->
  Onto f a b -> card b :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1 H2.
  (* Reindex the surjection by a bijection from card(a) onto a.                 *)
  assert (card a :~: a) as H3. { apply Equiv.Sym, IsEquiv. assumption. }
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
  rewrite H8. rewrite <- (Idem a). apply InclCompat. 2: assumption.
  exists (card a). split. 1: apply IsOrdinal. apply Equiv.Refl.
Qed.
(* The cardinal of an image of a well-orderable set is bounded.                 *)
Proposition ImageIncl : forall (F:Class) (a:U), WellOrderable a ->
  CRL.Functional F -> card F:[a]: :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros F a H1 H2.
  (* The restriction of F to a surjects from its domain onto its range.         *)
  assert (Onto (F:|:a) (SRD.domain (F:|:a)) (SRR.range (F:|:a))) as H3. {
    split. 2: reflexivity. split. 2: reflexivity.
    apply RestrictOfClass.IsFunction. assumption. }
  (* That range is the image of a, and its domain is contained in a.            *)
  assert (SRR.range (F:|:a) = F:[a]:) as H4. {
    apply RestrictOfClass.RangeOf. assumption. }
  assert (SRD.domain (F:|:a) :<=: a) as H5. {
    apply RestrictOfClass.DomainIsIncl. assumption. }
  (* The subdomain is well-orderable, so the surjection gives the bound.        *)
  assert (WellOrderable (SRD.domain (F:|:a))) as H6. {
    apply SCW.InclCompat with a; assumption. }
  assert (card (SRR.range (F:|:a)) :<=: card (SRD.domain (F:|:a))) as H7. {
    apply WhenOnto with (F:|:a); assumption. }
  assert (card (SRD.domain (F:|:a)) :<=: card a) as H8. {
    apply InclCompat; assumption. }
  rewrite <- H4. apply Incl.Tran with (card (SRD.domain (F:|:a))); assumption.
Qed.

(* A one-to-one class preserves the cardinal of a set contained in its domain.  *)
Proposition ImageInj : forall (F:Class) (a:U),
  CRO.OneToOne F               ->
  toClass a :<=: CRD.domain F  ->
  card F:[a]: = card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros F a H1 H2.
  (* The set and its image are equipotent, so their cardinals agree.            *)
  apply WhenEquiv. apply Equiv.Sym. apply Equiv.ImageInj; assumption.
Qed.
(* For well-orderable sets, a union is bounded by the disjoint sum.             *)
Proposition UnionSum : forall (a b:U), WellOrderable a -> WellOrderable b ->
  card (a :\/: b) :<=: card (a :++: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2.
  (* The disjoint sum of the two sets is again well-orderable.                  *)
  assert (WellOrderable (a :++: b)) as H3. {
    apply SCW.Sum; assumption. }
  remember (either a b (id a) (id b)) as f eqn:H4.
  (* The either map from the disjoint sum onto the ordinary union is onto.      *)
  assert (Onto f (a :++: b) (a :\/: b)) as H5. { rewrite H4. apply SMS.HasOnto. }
  (* A surjection from a well-orderable domain bounds its range cardinal.       *)
  apply WhenOnto with f; assumption.
Qed.
(* If a and b each have at least two elements, card(a ++ b) <= card(a x b).     *)
Proposition SumProd : forall (a b:U),
  :1: :< card a                         ->
  :1: :< card b                         ->
  card (a :++: b) :<=: card (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2.
  (* A non-zero cardinal makes each set equipotent to its cardinal.             *)
  assert (card a <> :0:) as H3. {
    intros H3. rewrite H3 in H1. apply Empty.Charac in H1. contradiction. }
  assert (card b <> :0:) as H4. {
    intros H4. rewrite H4 in H2. apply Empty.Charac in H2. contradiction. }
  assert (WellOrderable a) as H5. { apply WellOrderableNotZero. assumption. }
  assert (WellOrderable b) as H6. { apply WellOrderableNotZero. assumption. }
  (* The product is well-orderable, so an injection into it gives a bound.      *)
  assert (WellOrderable (a :x: b)) as H7. {
    apply SCW.Prod; assumption. }
  assert (exists f, Inj f (a :++: b) (a :x: b)) as H8. {
    apply SMS.HasInj; apply HasTwoElems; assumption. }
  destruct H8 as [f H8].
  apply WhenInj with f; assumption.
Qed.

(* If a and b each have at least two elements, card(a \/ b) <= card(a x b).     *)
Proposition UnionProd : forall (a b:U),
  :1: :< card a                         ->
  :1: :< card b                         ->
  card (a :\/: b) :<=: card (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2.
  (* The hypotheses make both sets well-orderable, without global choice.       *)
  assert (card a <> :0:) as H3. {
    intros H3. rewrite H3 in H1. apply Empty.Charac in H1. contradiction. }
  assert (card b <> :0:) as H4. {
    intros H4. rewrite H4 in H2. apply Empty.Charac in H2. contradiction. }
  assert (WellOrderable a) as H5. { apply WellOrderableNotZero. assumption. }
  assert (WellOrderable b) as H6. { apply WellOrderableNotZero. assumption. }
  (* The union is bounded by the sum, and the sum by the product.               *)
  apply Incl.Tran with (card (a :++: b)).
  - apply UnionSum; assumption.
  - apply SumProd; assumption.
Qed.

(* The cardinal of an ordinal containing omega also contains omega.             *)
Proposition CardOrdinal : forall (a:U), Ordinal a ->
  :N :<=: a -> :N :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1 H2.
  assert (Ordinal (card a)) as H3. { apply IsOrdinal. }
  assert (Ordinal :N) as H4. { apply Omega.IsOrdinal. }
  assert (card a :< :N \/ :N :<=: card a) as H5. {
    apply SOC.ElemOrIncl; assumption. }
  destruct H5 as [H5|H5]. 2: assumption.
  exfalso.
  assert (a :~: card a) as H6. { apply IsEquivOrd. assumption. }
  assert (a = card a) as H7. { apply SCE.EqualOrdNat; assumption. }
  assert (card a :< a) as H8. { apply H2. assumption. }
  rewrite <- H7 in H8. revert H8. apply Foundation.NoLoop1.
Qed.

Proposition NatCharac : forall (a:U), Ordinal a ->
  card a :< :N <-> a :< :N.
Proof.
  intros a H1.
  assert (Ordinal :N) as G1. { apply Omega.IsOrdinal. }
  split; intros H2.
  - assert (a :< :N \/ :N :<=: a) as H3. { apply SOC.ElemOrIncl; assumption. }
    destruct H3 as [H3|H3]. 1: assumption.
    apply CardOrdinal in H3. 2: assumption. exfalso.
    assert (card a :< card a) as H4. { apply H3. assumption. } revert H4.
    apply Foundation.NoLoop1.
  - assert (card a = a) as H3. { apply WhenNat. assumption. }
    rewrite H3. assumption.
Qed.

(* Lower half of Square: an infinite ordinal embeds cardinally in its square.   *)
Proposition SquareHigher : forall (a:U), Ordinal a ->
  :N :<=: a -> card a :<=: card (a :x: a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1 H2.
  assert (:1: :< a) as H3. { apply H2. apply Omega.HasOne. }
  apply Incl.Tran with (card (succ a)).
  - apply IsInclSucc.
  - apply SuccSquare; assumption.
Qed.

(* Cardinal equality is compatible with products of well-orderable sets.        *)
Proposition ProdCompat : forall (a b c d:U),
  WellOrderable a                   ->
  WellOrderable b                   ->
  WellOrderable c                   ->
  WellOrderable d                   ->
  card a = card c                   ->
  card b = card d                   ->
  card (a :x: b) = card (c :x: d).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c d H1 H2 H3 H4 H5 H6.
  (* The two product sets are well-orderable.                                   *)
  apply EquivCharac.
  - apply SCW.Prod; assumption.
  - apply SCW.Prod; assumption.
  - (* Equal cardinals identify each pair of corresponding factors up to        *)
    (* equipotence, and products preserve equipotence.                          *)
    apply SCE.ProdCompat.
    + apply EquivCharac; assumption.
    + apply EquivCharac; assumption.
Qed.

(* Cardinal equality is compatible with a product on the right.                 *)
Proposition ProdCompatL : forall (a b c:U),
  WellOrderable a                   ->
  WellOrderable b                   ->
  WellOrderable c                   ->
  card a = card b                   ->
  card (a :x: c) = card (b :x: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c H1 H2 H3 H4.
  (* Keep the right factor fixed and use reflexivity on its cardinal.           *)
  apply ProdCompat; try assumption. reflexivity.
Qed.

(* Cardinal equality is compatible with a product on the left.                  *)
Proposition ProdCompatR : forall (a b c:U),
  WellOrderable a                   ->
  WellOrderable b                   ->
  WellOrderable c                   ->
  card a = card b                   ->
  card (c :x: a) = card (c :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c H1 H2 H3 H4.
  (* Keep the left factor fixed and use reflexivity on its cardinal.            *)
  apply ProdCompat; try assumption. reflexivity.
Qed.


Proposition Square : forall (a:U), Ordinal a ->
  :N :<=: a -> card (a :x: a) = card a.
Proof.
  remember (fun a => a :< :N \/ card (a :x: a) = card a) as A eqn:H1.
  assert (forall a, Ordinal a -> A a) as H2. {
    apply Induction.Induction. intros a H2 IH. rewrite H1 in IH.
    assert (WellOrderable a) as G1. { apply SCW.WhenOrdinal. assumption. }
    assert (WellOrderable (a :x: a)) as G2. { apply SCW.Prod; assumption. }
    assert (CRO.OneToOne Pairing) as G3. { apply MaxLex.IsIsom. }
    assert (toClass (a :x: a) :<=: CRD.domain Pairing) as G4. {
      apply MaxLex.IsIncl; assumption. }
    assert (Ordinal :N) as G5. { apply Omega.IsOrdinal. }
    assert (Ordinal (card a)) as G6. { apply IsOrdinal. }
    assert (WellOrderable (card a)) as G7. {
      apply SCW.WhenOrdinal. assumption. }
    assert (card (card a) = card a) as G8. { apply Idem. }
    assert (CRO.OneToOne Pairing) as G10. { apply IsIsom. }
    assert (forall b, b :< a -> card b :<=: card a) as H3. {
      intros b H3.
      assert (Ordinal b) as K1. { apply SOC.IsOrdinal with a; assumption. }
      apply InclCompat. 1: assumption. apply SOC.ElemIsIncl; assumption. }
    assert ((exists b, b :< a /\ card b = card a) \/
          ~(exists b, b :< a /\ card b = card a)) as [H4|H4]. {
      apply LawExcludedMiddle. }
    - destruct H4 as [b [H4 H5]].
      assert (Ordinal b) as K1. { apply SOC.IsOrdinal with a; assumption. }
      assert (WellOrderable b) as K2. { apply SCW.WhenOrdinal. assumption. }
      assert (card (b :x: b) = card (a :x: a)) as K3. {
        apply ProdCompat; assumption. }
      specialize (IH b H4). destruct IH as [IH|IH]; rewrite H1.
      + left. apply NatCharac. 1: assumption. rewrite <- H5.
        apply NatCharac; assumption.
      + right. rewrite <- K3, IH. assumption.
    - assert (forall b, b :< a -> card b :< card a) as H5. {
        intros b H5.
        assert (Ordinal b) as K1. { apply SOC.IsOrdinal with a; assumption. }
        assert (Ordinal (card a)) as K2. { apply IsOrdinal. }
        assert (Ordinal (card b)) as K3. { apply IsOrdinal. }
        assert (card b = card a \/ card b :< card a) as K4. {
          apply SOC.EqualOrElem; try assumption. apply H3. assumption. }
        destruct K4 as [K4|K4]. 2: assumption. exfalso. apply H4.
        exists b. split; assumption. }
      assert (forall b,
        b :< a        ->
        :N :<=: b     ->
        card (succ b :x: succ b) = card (succ b)) as H6. {
        intros b H6 H7.
        assert (Ordinal b) as K1. { apply SOC.IsOrdinal with a; assumption. }
        assert (Ordinal (succ b)) as K2. { apply Succ.IsOrdinal. assumption. }
        assert (Cardinal (card a)) as K3. { exists a. reflexivity. }
        assert (card b = card (succ b)) as K4. { apply Succ; assumption. }
        assert (Ordinal (card a)) as K5. { apply IsOrdinal. }
        assert (succ b :< card a) as H8. {
          apply CardLess; try assumption. rewrite <- K4. apply H5. assumption. }
        assert (succ b :< a) as H9. {
          apply SOC.ElemInclTran with (card a); try assumption.
          apply IsIncl. assumption. }
        specialize (IH (succ b) H9).
        destruct IH as [IH|IH]. 2: assumption. exfalso.
        assert (succ b :< b) as H10. { apply H7. assumption. }
        assert (succ b :< succ b) as H11. { apply Succ.IsIncl. assumption. }
        revert H11. apply Foundation.NoLoop1. }
      assert (a :< :N \/ :N :<=: a) as G9. { apply SOC.ElemOrIncl; assumption. }
      destruct G9 as [G9|G9]. 1: { rewrite H1. left. assumption. }
      assert (Pairing:[a :x: a]: :<=: card a) as H7. {
        intros d H7.
        apply (CRB.ImageSetCharac _ (Ordinal :x: Ordinal) Ordinal) in H7.
        2: apply IsIsom. destruct H7 as [x [H7 [H8 H9]]].
        apply Prod.Charac in H7. destruct H7 as [b [c [H7 [H10 H11]]]].
        subst x d. apply CPR.Charac2 in H8. destruct H8 as [H8 H12].

        assert (Pairing :[initSegment MaxLex (Ordinal :x: Ordinal) :(b,c):]:  =
          Pairing!:(b,c):) as H7. { apply MaxLex.PairingInit; assumption. }
        assert (
          card (Pairing :[initSegment MaxLex (Ordinal :x: Ordinal) :(b,c):]:) =
          card (initSegment MaxLex (Ordinal :x: Ordinal) :(b,c):)) as H13. {
          apply ImageInj.
Admitted.

(*
      assert (card (Pairing :[a :x: a]:) = card (a :x: a)) as H8. {
        apply ImageInj; assumption. }
      assert (card (Pairing :[a :x: a]:) :<=: card a) as H9. {
        rewrite <- G8. apply InclCompat; assumption. }
      assert (card (a :x: a) :<=: card a) as H10. {
        rewrite <- H8. assumption. }
      rewrite H1. assert (a :< :N \/ :N :<=: a) as H11. {
        apply SOC.ElemOrIncl; assumption. }
      destruct H11 as [H11|H11]. 1: { left. assumption. } right.
      assert (card a :<=: card (a :x: a)) as H12. {
        apply SquareHigher; assumption. }
      apply Incl.Double. split; assumption. }
  intros a H3 H4. rewrite H1 in H2. specialize (H2 a H3).
  destruct H2 as [H2|H2]. 2: assumption.
  assert (a :< a) as H5. { apply H4. assumption. }
  exfalso. revert H5. apply Foundation.NoLoop1.
Admitted.
                                                                                *)
