Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Set.Cardinal.Equip.
Require Import ZF.Set.Cardinal.Infinite.
Require Import ZF.Set.Cardinal.Map.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Cardinal.WithChoice.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Single.
Require Import ZF.Set.Relation.Charac.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Fiber.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Map.
Require Import ZF.Set.Relation.Map.Curry.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Exp2.
Export ZF.Notation.Exp2.


(* The exponentiation of two sets.                                              *)
Definition exp (a b:U) : U := map b a.


(* Notation "a :^^: b" := (exp a b)                                             *)
Global Instance SetExp2 : Exp2 U := { exp2 := exp }.

(* Exponentiation is compatible with equipotence in both arguments.             *)
Proposition Compat : forall (a b c d:U),
  a :~: c -> b :~: d -> a :^^: b :~: c :^^: d.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c d H1 H2.
  (* This is exactly compatibility of the corresponding set of maps.            *)
  apply Cardinal.Map.Compat; assumption.
Qed.

(* Exponentiation is left-compatible with equipotence.                          *)
Proposition CompatL : forall (a b c:U),
  a :~: b -> a :^^: c :~: b :^^: c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c H1.
  (* Changing the base changes the codomain of the map set.                     *)
  apply Cardinal.Map.CompatR. assumption.
Qed.

(* Exponentiation is right-compatible with equipotence.                         *)
Proposition CompatR : forall (a b c:U),
  b :~: c -> a :^^: b :~: a :^^: c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c H1.
  (* Changing the exponent changes the domain of the map set.                   *)
  apply Cardinal.Map.CompatL. assumption.
Qed.

(* Exponentiation is cardinal-compatible in both arguments under choice.        *)
Proposition CompatCard : forall (a b c d:U),
  Choice                                ->
  card a = card c                       ->
  card b = card d                       ->
  card (a :^^: b) = card (c :^^: d).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c d AC H1 H2.
  (* Choice turns the cardinal equalities into equipotences.                    *)
  assert (a :~: c) as H3. { apply WithChoice.EquipCharac; assumption. }
  assert (b :~: d) as H4. { apply WithChoice.EquipCharac; assumption. }
  (* The structural compatibility then identifies the function sets.            *)
  apply Number.WhenEquip. apply Compat; assumption.
Qed.

(* Exponentiation is left cardinal-compatible under choice.                     *)
Proposition CompatCardL : forall (a b c:U),
  Choice                                ->
  card a = card b                       ->
  card (a :^^: c) = card (b :^^: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* Choice turns the base cardinal equality into an equipotence.               *)
  assert (a :~: b) as H2. { apply WithChoice.EquipCharac; assumption. }
  (* The structural left compatibility then identifies the function sets.       *)
  apply Number.WhenEquip. apply CompatL. assumption.
Qed.

(* Exponentiation is right cardinal-compatible under choice.                    *)
Proposition CompatCardR : forall (a b c:U),
  Choice                                ->
  card b = card c                       ->
  card (a :^^: b) = card (a :^^: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* Choice turns the exponent cardinal equality into an equipotence.           *)
  assert (b :~: c) as H2. { apply WithChoice.EquipCharac; assumption. }
  (* The structural right compatibility then identifies the function sets.      *)
  apply Number.WhenEquip. apply CompatR. assumption.
Qed.

(* Exponentiation by one is equipotent to the base.                             *)
Proposition WhenOneR : forall (a:U),
  a :^^: :1: :~: a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a.
  (* Send an element of a to the constant map on the singleton.                 *)
  remember (fun y => from :1: (fun _ => y)) as F eqn:H1.
  remember (from a F) as h eqn:H2.
  assert (:0: :< :1:) as H3. {
    rewrite Natural.OneExtension. apply Single.IsIn. }
  (* Each displayed constant map is a map from one into a.                      *)
  assert (forall y, y :< a -> F y :< map :1: a) as H4. {
    intros y H4. rewrite H1. apply CharacMap. apply From.IsFun.
    intros x H5. assumption. }
  (* Equal constant maps have equal values at the unique element of one.        *)
  assert (forall x y,
    x :< a -> y :< a -> F x = F y -> x = y) as H5. {
    intros x y H5 H6 H7. rewrite H1 in H7.
    assert ((from :1: (fun _ => x))!:0: = (from :1: (fun _ => y))!:0:) as H8. {
      rewrite H7. reflexivity. }
    rewrite From.Eval in H8. 2: assumption.
    rewrite From.Eval in H8. 2: assumption. assumption. }
  (* Any map from one into a is the constant map at its value on zero.          *)
  assert (forall f,
    f :< map :1: a -> exists y, y :< a /\ F y = f) as H6. {
    intros f H6.
    assert (Fun f :1: a) as H7. { apply CharacMap. assumption. }
    exists (f!:0:). split.
    - apply Fun.IsInRange with :1:; assumption.
    - rewrite H1.
      apply Fun.Equal with :1: a :1: a; try reflexivity; try assumption.
      + apply From.IsFun. intros x H8. apply Fun.IsInRange with :1:; assumption.
      + intros x H8. rewrite From.Eval. 2: assumption.
        assert (x = :0:) as H9. {
          rewrite Natural.OneExtension in H8. apply Single.Charac. assumption. }
        rewrite H9. reflexivity. }
  assert (Bij h a (map :1: a)) as H7. {
    rewrite H2. apply From.IsBij; assumption. }
  apply Equip.Sym. exists h. assumption.
Qed.

(* Exponentiation by one has the cardinal of the base.                          *)
Proposition WhenOneCardR : forall (a:U),
  card (a :^^: :1:) = card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a.
  (* Equal sets of size are represented by the same cardinal.                   *)
  apply Number.WhenEquip. apply WhenOneR.
Qed.

(* The set of two-valued maps on a is equipotent to the power set of a.         *)
Proposition WhenTwoL : forall (a:U),
  :2: :^^: a :~: :P(a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* Send a two-valued function to its fiber over one.                          *)
  intros a.
  remember (from (map a :2:) (fun f => fiber f :1:)) as h eqn:H1.
  assert (Bij h (map a :2:) :P(a)) as H2. {
    rewrite H1. apply From.IsBij.
    - (* The fiber over one is a subset of the domain, hence a subset of a.     *)
      intros f H2. apply Power.Charac.
      assert (Fun f a :2:) as H3. { apply CharacMap. assumption. }
      assert (domain f = a) as H4. { apply H3. }
      rewrite <- H4. apply Fiber.IsIncl.
    - (* Binary-valued functions are determined by their fibers over one.       *)
      intros f g H2 H3 H4. apply Fiber.EqualOfOne with a; try assumption;
        apply CharacMap; assumption.
    - (* Every subset of a is the fiber over one of its characteristic function.*)
      intros b H2.
      assert (b :<=: a) as H3. { apply Power.Charac. assumption. }
      exists (charac a b). split.
      + apply CharacMap. apply Charac.IsFun.
      + apply Fiber.OfCharac. assumption. }
  exists h. assumption.
Qed.

(* The two-valued maps on a have the power-set cardinal.                        *)
Proposition WhenTwoCardL : forall (a:U),
  card (:2: :^^: a) = card :P(a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a.
  (* Equal sets of size are represented by the same cardinal.                   *)
  apply Number.WhenEquip. apply WhenTwoL.
Qed.

(* Currying identifies maps into a function set with maps on a product.         *)
Proposition Assoc : forall (a b c:U),
  (a :^^: b) :^^: c :~: a :^^: (b :x: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* First use the standard currying bijection with the product ordered c x b.  *)
  intros a b c.
  assert (map c (map b a) :~: map (c :x: b) a) as H1. {
    apply Equip.Sym. exists (curryMap c b a). apply Curry.IsBijMap. }
  (* Then commute the product inside the exponent.                              *)
  assert (map (c :x: b) a :~: map (b :x: c) a) as H2. {
    apply CompatR. apply Equip.ProdComm. }
  apply Equip.Tran with (map (c :x: b) a); assumption.
Qed.

(* Currying identifies the cardinals of the associated function sets.           *)
Proposition AssocCard : forall (a b c:U),
  card ((a :^^: b) :^^: c) = card (a :^^: (b :x: c)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c.
  (* Equipotent function sets have the same cardinal.                           *)
  apply Number.WhenEquip. apply Assoc.
Qed.

(* Exponentiation is left-monotone in cardinal under choice.                    *)
Proposition InclCompatCardL : forall (a b c:U),
  Choice                                ->
  card a :<=: card b                    ->
  card (a :^^: c) :<=: card (b :^^: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* The cardinal inequality gives an injection from a into b.                  *)
  assert (exists f, Inj f a b) as H2. {
    apply WithChoice.HasInj; assumption. }
  destruct H2 as [f H2].
  (* Postcomposition with that injection embeds maps c -> a into maps c -> b.   *)
  assert (exists h, Inj h (map c a) (map c b)) as H3. {
    apply (Relation.Map.HasInjR a b c f). assumption. }
  destruct H3 as [h H3].
  (* An injection of the function spaces gives the cardinal inequality.         *)
  apply WithChoice.WhenInj with h; assumption.
Qed.

(* Exponentiation is right-monotone in cardinal under choice.                   *)
Proposition InclCompatCardR : forall (a b c:U),
  Choice                                ->
  b <> :0:                              ->
  card b :<=: card c                    ->
  card (a :^^: b) :<=: card (a :^^: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1 H2.
  (* The cardinal inequality gives a surjection from c onto b.                  *)
  assert (exists f, Onto f c b) as H3. {
    apply WithChoice.HasOnto; assumption. }
  destruct H3 as [f H3].
  (* Precomposition with that surjection embeds maps b -> a into maps c -> a.   *)
  assert (exists h, Inj h (map b a) (map c a)) as H4. {
    apply (Relation.Map.HasInjL c b a f). assumption. }
  destruct H4 as [h H4].
  (* An injection of the function spaces gives the cardinal inequality.         *)
  apply WithChoice.WhenInj with h; assumption.
Qed.

(* Exponentiation is monotone in both cardinal arguments under choice.          *)
Proposition InclCompatCard : forall (a b c d:U),
  Choice                                ->
  c <> :0:                              ->
  card a :<=: card b                    ->
  card c :<=: card d                    ->
  card (a :^^: c) :<=: card (b :^^: d).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c d AC H1 H2 H3.
  (* First enlarge the base, then enlarge the exponent.                         *)
  apply Incl.Tran with (card (b :^^: c)).
  - apply InclCompatCardL; assumption.
  - apply InclCompatCardR; assumption.
Qed.

(* A power-set base raised to an infinite exponent has its own size.            *)
Proposition WhenPowerSetL : forall (a:U),
  Choice                            ->
  Infinite a                        ->
  :P(a) :^^: a :~: :P(a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC H1.
  (* An infinite set has cardinal at least omega under choice.                  *)
  assert (:N :<=: card a) as H2. { apply Infinite.Card; assumption. }
  (* Hence its square has the same cardinal.                                    *)
  assert (card (a :x: a) = card a) as H3. { apply Number.Square. assumption. }
  (* Under choice this cardinal equality gives an equipotence of exponents.     *)
  assert (a :x: a :~: a) as H4. {
    apply WithChoice.EquipCharac; assumption. }
  (* Replace P(a) by 2^a as the base.                                           *)
  assert (:P(a) :^^: a :~: (:2: :^^: a) :^^: a) as H5. {
    apply CompatL. apply Equip.Sym. apply WhenTwoL. }
  (* Associate the two exponentiations into one exponent over a x a.            *)
  assert ((:2: :^^: a) :^^: a :~: :2: :^^: (a :x: a)) as H6. {
    apply Assoc. }
  (* The square exponent has the same size as the original exponent.            *)
  assert (:2: :^^: (a :x: a) :~: :2: :^^: a) as H7. {
    apply CompatR. assumption. }
  (* Finally translate 2^a back to the power set of a.                          *)
  assert (:2: :^^: a :~: :P(a)) as H8. { apply WhenTwoL. }
  apply Equip.Tran with ((:2: :^^: a) :^^: a). 1: assumption.
  apply Equip.Tran with (:2: :^^: (a :x: a)). 1: assumption.
  apply Equip.Tran with (:2: :^^: a); assumption.
Qed.

(* A power-set base raised to an infinite exponent has its own cardinal.        *)
Proposition WhenPowerSetCardL : forall (a:U),
  Choice                            ->
  Infinite a                        ->
  card (:P(a) :^^: a) = card :P(a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC H1.
  (* Equipotent sets have the same cardinal.                                    *)
  apply Number.WhenEquip. apply WhenPowerSetL; assumption.
Qed.

(* A bounded nontrivial base has the power-set cardinal.                        *)
Proposition WhenBoundedCardL : forall (a b:U),
  Choice                                ->
  Infinite b                            ->
  :2: :<=: card a                       ->
  card a :<=: card :P(b)                ->
  card (a :^^: b) = card :P(b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1 H2 H3.
  (* The lower bound compares 2^b with a^b, then identifies 2^b with P(b).      *)
  assert (card :P(b) :<=: card (a :^^: b)) as H4. {
    assert (card :2: :<=: card a) as G1. {
      rewrite Number.WhenNat. 2: { apply Omega.HasSucc, Omega.HasOne. }
      assumption. }
    assert (card (:2: :^^: b) :<=: card (a :^^: b)) as H4. {
      apply (InclCompatCardL :2: a b); assumption. }
    assert (card (:2: :^^: b) = card :P(b)) as H5. { apply WhenTwoCardL. }
    rewrite <- H5. assumption. }
  (* The upper bound compares a^b with P(b)^b, then evaluates P(b)^b.           *)
  assert (card (a :^^: b) :<=: card :P(b)) as H5. {
    assert (card (a :^^: b) :<=: card (:P(b) :^^: b)) as H5. {
      apply (InclCompatCardL a :P(b) b); assumption. }
    assert (card (:P(b) :^^: b) = card :P(b)) as H6. {
      apply WhenPowerSetCardL; assumption. }
    rewrite <- H6. assumption. }
  (* The two cardinal bounds identify the cardinals.                            *)
  apply Incl.Double. split; assumption.
Qed.

(* Aleph bases below an Aleph exponent have the same power as two.              *)
Proposition WhenAlephInclL : forall (a b:U),
  Choice                                                  ->
  Ordinal a                                               ->
  Ordinal b                                               ->
  Aleph!a :<=: Aleph!b                                    ->
  card (Aleph!a :^^: Aleph!b) = card (:2: :^^: Aleph!b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1 H2 H3.
  assert (InfiniteCard Aleph!a) as G1. { apply Aleph.IsInfiniteCard. assumption. }
  assert (Cardinal Aleph!a) as G2. { apply Aleph.IsCardinal. assumption. }
  assert (Ordinal Aleph!a) as G3. { apply Aleph.IsOrdinal. assumption. }
  assert (Cardinal Aleph!b) as G4. { apply Aleph.IsCardinal. assumption. }
  (* The smaller Aleph is at least two, because every Aleph contains N.         *)
  assert (:2: :<=: card Aleph!a) as H4. {
    assert (Aleph!a = card Aleph!a) as K1. {
      apply Number.WhenCardinal. assumption. }
    rewrite <- K1.
    assert (:N :<=: Aleph!a) as K2. { apply InfiniteCard.IsIncl. assumption. }
    assert (:2: :< Aleph!a) as K3. { apply K2. apply Omega.HasTwo. }
    apply Ordinal.ElemIsIncl; assumption. }
  (* The upper bound follows from Aleph inclusion and Cantor's theorem.         *)
  assert (card Aleph!a :<=: card :P(Aleph!b)) as H5. {
    assert (Aleph!a = card Aleph!a) as K1. {
      apply Number.WhenCardinal. assumption. }
    assert (Aleph!b = card Aleph!b) as K2. {
      apply Number.WhenCardinal. assumption. }
    assert (card Aleph!b :< card :P(Aleph!b)) as K3. {
      apply WithChoice.Cantor. assumption. }
    assert (Ordinal (card :P(Aleph!b))) as K4. { apply Number.IsOrdinal. }
    assert (card Aleph!b :<=: card :P(Aleph!b)) as K5. {
      apply Ordinal.ElemIsIncl; assumption. }
    rewrite <- K1. apply Incl.Tran with Aleph!b. 1: assumption.
    rewrite <- K2 in K5. assumption. }
  (* The bounded theorem identifies the left side with P(Aleph b).              *)
  assert (card (Aleph!a :^^: Aleph!b) = card :P(Aleph!b)) as H6. {
    apply WhenBoundedCardL; try assumption. apply Aleph.IsInfinite. assumption. }
  (* Finally replace the power set by the two-valued function set.              *)
  assert (card (:2: :^^: Aleph!b) = card :P(Aleph!b)) as H7. {
    apply WhenTwoCardL. }
  rewrite H7. assumption.
Qed.

(* An Aleph to its own power has the same power as two to that Aleph.           *)
Proposition AlephSame : forall (a:U),
  Choice                                                  ->
  Ordinal a                                               ->
  card (Aleph!a :^^: Aleph!a) = card (:2: :^^: Aleph!a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC H1.
  (* This is the equal-index case of the previous Aleph comparison theorem.     *)
  apply WhenAlephInclL; try assumption. apply Incl.Refl.
Qed.

(* A larger Aleph raised to a smaller Aleph is bounded by two to the larger.    *)
Proposition WhenAlephInclR : forall (a b:U),
  Choice                                                  ->
  Ordinal a                                               ->
  Ordinal b                                               ->
  Aleph!a :<=: Aleph!b                                    ->
  card (Aleph!b :^^: Aleph!a) :<=: card (:2: :^^: Aleph!b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1 H2 H3.
  assert (InfiniteCard Aleph!a) as G1. { apply Aleph.IsInfiniteCard. assumption. }
  assert (Cardinal Aleph!a) as G2. { apply Aleph.IsCardinal. assumption. }
  assert (Cardinal Aleph!b) as G3. { apply Aleph.IsCardinal. assumption. }
  (* The smaller Aleph is non-empty, because every Aleph is infinite.           *)
  assert (Aleph!a <> :0:) as H4. { apply InfiniteCard.IsNotZero. assumption. }
  (* The inclusion of Alephs is the same as the corresponding cardinal bound.   *)
  assert (card Aleph!a :<=: card Aleph!b) as H5. {
    assert (Aleph!a = card Aleph!a) as K1. {
      apply Number.WhenCardinal. assumption. }
    assert (Aleph!b = card Aleph!b) as K2. {
      apply Number.WhenCardinal. assumption. }
    rewrite <- K1, <- K2. assumption. }
  (* Monotonicity in the exponent bounds the reversed Aleph power.              *)
  assert (card (Aleph!b :^^: Aleph!a) :<=: card (Aleph!b :^^: Aleph!b)) as H6. {
    apply InclCompatCardR; assumption. }
  (* The diagonal Aleph power is the same size as the two-valued power.         *)
  assert (card (Aleph!b :^^: Aleph!b) = card (:2: :^^: Aleph!b)) as H7. {
    apply AlephSame; assumption. }
  rewrite <- H7. assumption.
Qed.
