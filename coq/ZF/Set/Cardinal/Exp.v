Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Continuum.
Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Set.Cardinal.Equip.
Require Import ZF.Set.Cardinal.Infinite.
Require Import ZF.Set.Cardinal.Map.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Cardinal.Regular.
Require Import ZF.Set.Cardinal.Successor.
Require Import ZF.Set.Cardinal.WithChoice.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.ProdGen.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Ordinal.Cofinal.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Monotone.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Single.
Require Import ZF.Set.Relation.Charac.
Require Import ZF.Set.Ordinal.Character.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Fiber.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Map.
Require Import ZF.Set.Relation.Map.Curry.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Union.
Require Import ZF.Set.UnionGenOfClass.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Exp2.
Export ZF.Notation.Exp2.


Module CFF := ZF.Class.Relation.Fun.From.


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
    intros y H4. rewrite H1. apply Map.CharacMap. apply From.IsFun.
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
    assert (Fun f :1: a) as H7. { apply Map.CharacMap. assumption. }
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

(* A non-empty exponent contains a copy of the base cardinal.                   *)
Proposition IsInclCardR : forall (a b:U),
  Choice                            ->
  b <> :0:                          ->
  card a :<=: card (a :^^: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Choose one point of the exponent and send each base element to a constant. *)
  assert (exists x, x :< b) as H2. { apply Empty.HasElem. assumption. }
  destruct H2 as [x H2].
  remember (fun y => from b (fun _ => y)) as F eqn:H3.
  remember (from a F) as h eqn:H4.
  assert (Inj h a (map b a)) as H5. {
    (* Each displayed constant is a function from b into a.                     *)
    assert (forall y, y :< a -> F y :< map b a) as H5. {
      intros y H5. rewrite H3. apply Map.CharacMap. apply From.IsFun.
      intros z H6. assumption. }
    (* Equal constant functions have equal values at the chosen point.          *)
    assert (forall y z,
      y :< a -> z :< a -> F y = F z -> y = z) as H6. {
      intros y z H6 H7 H8.
      assert ((F y)!x = (F z)!x) as H9. { rewrite H8. reflexivity. }
      rewrite H3, From.Eval, From.Eval in H9; assumption. }
    rewrite H4. apply From.IsInj; assumption. }
  apply WithChoice.WhenInj with h; assumption.
Qed.

(* A non-empty exponent of an infinite-cardinal base is infinite.               *)
Proposition IsInfiniteCard : forall (a b:U),
  Choice                            ->
  InfiniteCard (card a)             ->
  b <> :0:                          ->
  InfiniteCard (card (a :^^: b)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1 H2.
  (* The base cardinal already contains omega.                                  *)
  assert (:N :<=: card a) as H3. { apply InfiniteCard.IsIncl. assumption. }
  (* Constant functions embed the base cardinal into the exponent.              *)
  assert (card a :<=: card (a :^^: b)) as H4. {apply IsInclCardR; assumption. }
  (* Hence omega is contained in the exponent cardinal as well.                 *)
  assert (:N :<=: card (a :^^: b)) as H5. {
    apply Incl.Tran with (card a); assumption. }
  (* Any cardinal containing omega is an infinite cardinal.                     *)
  apply InfiniteCard.WhenIncl. 2: assumption. exists (a :^^: b). reflexivity.
Qed.

(* At a limit Aleph base, exponentiation is the union of earlier powers.        *)
Proposition WhenLimitAlephL : forall (a b:U),
  Limit a                                                   ->
  Ordinal b                                                 ->
  b :< charac (Aleph!a)                                     ->
  Aleph!a :^^: b = :\/:_{a} :[fun c => Aleph!c :^^: b]:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2 H3.
  assert (Ordinal a) as G1. { apply H1. }
  assert (Ordinal Aleph!a) as G2. { apply Aleph.IsOrdinal. assumption. }
  assert (Aleph!a = :\/:_{a} Aleph) as H4. { apply Aleph.Continuous. assumption. }
  (* Every map into Aleph(a) is already bounded by some earlier Aleph value.    *)
  assert (Aleph!a :^^: b :<=: :\/:_{a} :[fun c => Aleph!c :^^: b]:) as H5. {
    intros f H5.
    assert (Fun f b Aleph!a) as H6. { apply Map.CharacMap. assumption. }
    assert (exists d, d :< Aleph!a /\ forall x, x :< b -> f!x :< d) as H7. {
      apply Character.WhenLess; assumption. }
    destruct H7 as [d [H7 H8]]. rewrite H4 in H7.
    apply UnionGenOfClass.Charac in H7. destruct H7 as [c [H7 H9]].
    assert (Ordinal c) as H10. { apply (Ordinal.IsOrdinal a); assumption. }
    assert (Ordinal Aleph!c) as H11. { apply Aleph.IsOrdinal. assumption. }
    assert (Ordinal d) as H12. { apply Ordinal.IsOrdinal with Aleph!c; assumption. }
    assert (d :<=: Aleph!c) as H13. { apply Ordinal.ElemIsIncl; assumption. }
    assert (Fun f b d) as H14. {
      split. 1: apply H6. intros y H14.
      apply (Fun.RangeCharac f b Aleph!a) in H14. 2: assumption.
      destruct H14 as [x [H14 H15]]. rewrite <- H15. apply H8. assumption. }
    assert (Fun f b Aleph!c) as H15. { apply Fun.InclCompatR with d; assumption. }
    apply UnionGenOfClass.Charac. exists c. split. 1: assumption.
    rewrite CFF.Eval. apply Map.CharacMap. assumption. }
  (* Conversely, a map into an earlier Aleph value is a map into Aleph(a).      *)
  assert (:\/:_{a} :[fun c => Aleph!c :^^: b]: :<=: Aleph!a :^^: b) as H6. {
    intros f H6. apply UnionGenOfClass.Charac in H6.
    destruct H6 as [c [H6 H7]]. rewrite CFF.Eval in H7.
    assert (Ordinal c) as H8. { apply (Ordinal.IsOrdinal a); assumption. }
    assert (c :<=: a) as H9. { apply Ordinal.ElemIsIncl; assumption. }
    assert (Aleph!c :<=: Aleph!a) as H10. { apply Aleph.InclCompat; assumption. }
    assert (Fun f b Aleph!c) as H11. { apply Map.CharacMap. assumption. }
    assert (Fun f b Aleph!a) as H12. {
      apply Fun.InclCompatR with Aleph!c; assumption. }
    apply Map.CharacMap. assumption. }
  apply Incl.Double. split; assumption.
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
      assert (Fun f a :2:) as H3. { apply Map.CharacMap. assumption. }
      assert (domain f = a) as H4. { apply H3. }
      rewrite <- H4. apply Fiber.IsIncl.
    - (* Binary-valued functions are determined by their fibers over one.       *)
      intros f g H2 H3 H4. apply Fiber.EqualOfOne with a; try assumption;
        apply Map.CharacMap; assumption.
    - (* Every subset of a is the fiber over one of its characteristic function.*)
      intros b H2.
      assert (b :<=: a) as H3. { apply Power.Charac. assumption. }
      exists (Charac.charac a b). split.
      + apply Map.CharacMap. apply Charac.IsFun.
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

(* Cantor's theorem bounds a set by its two-valued function set.                *)
Proposition CantorCard : forall (a:U), Choice ->
  card a :< card (:2: :^^: a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC.
  (* The two-valued function set has the same cardinal as the power set.        *)
  rewrite WhenTwoCardL. apply WithChoice.Cantor. assumption.
Qed.

(* Cantor's theorem bounds an Aleph by its two-valued function set.             *)
Proposition CantorAlephCard : forall (a:U), Choice ->
  Ordinal a -> Aleph!a :< card (:2: :^^: Aleph!a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC H1.
  (* First apply Cantor's theorem to the underlying Aleph set.                  *)
  assert (card Aleph!a :< card (:2: :^^: Aleph!a)) as H2. {
    apply CantorCard. assumption. }
  (* An Aleph is already its own cardinal, so this is the desired bound.        *)
  rewrite Aleph.Card in H2; assumption.
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
  Choice                           ->
  Infinite b                       ->
  :2: :<=: card a                  ->
  card a :<=: card :P(b)           ->
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
    rewrite Aleph.Card. 2: assumption.
    assert (:N :<=: Aleph!a) as K2. { apply InfiniteCard.IsIncl. assumption. }
    assert (:2: :< Aleph!a) as K3. { apply K2. apply Omega.HasTwo. }
    apply Ordinal.ElemIsIncl; assumption. }
  (* The upper bound follows from Aleph inclusion and Cantor's theorem.         *)
  assert (card Aleph!a :<=: card :P(Aleph!b)) as H5. {
    assert (card Aleph!b :< card :P(Aleph!b)) as K3. {
      apply WithChoice.Cantor. assumption. }
    assert (Ordinal (card :P(Aleph!b))) as K4. { apply Number.IsOrdinal. }
    assert (card Aleph!b :<=: card :P(Aleph!b)) as K5. {
      apply Ordinal.ElemIsIncl; assumption. }
    rewrite Aleph.Card. 2: assumption.
    apply Incl.Tran with Aleph!b. 1: assumption.
    rewrite Aleph.Card in K5; assumption. }
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
  Aleph!b :<=: Aleph!a                                    ->
  card (Aleph!a :^^: Aleph!b) :<=: card (:2: :^^: Aleph!a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1 H2 H3.
  assert (InfiniteCard Aleph!b) as G1. { apply Aleph.IsInfiniteCard. assumption. }
  assert (Cardinal Aleph!a) as G2. { apply Aleph.IsCardinal. assumption. }
  assert (Cardinal Aleph!b) as G3. { apply Aleph.IsCardinal. assumption. }
  (* The smaller Aleph is non-empty, because every Aleph is infinite.           *)
  assert (Aleph!b <> :0:) as H4. { apply InfiniteCard.IsNotZero. assumption. }
  (* The Aleph inclusion gives the corresponding cardinal bound.                *)
  assert (card Aleph!b :<=: card Aleph!a) as H5. {
    rewrite Aleph.Card, Aleph.Card; assumption. }
  (* Monotonicity in the exponent bounds the reversed Aleph power.              *)
  assert (card (Aleph!a :^^: Aleph!b) :<=: card (Aleph!a :^^: Aleph!a)) as H6. {
    apply InclCompatCardR; assumption. }
  (* The diagonal Aleph power is the same size as the two-valued power.         *)
  assert (card (Aleph!a :^^: Aleph!a) = card (:2: :^^: Aleph!a)) as H7. {
    apply AlephSame; assumption. }
  rewrite <- H7. assumption.
Qed.

(* A small Aleph exponent of a limit Aleph base has the base cardinal.          *)
Proposition IsAlephBase : forall (a b:U),
  Choice                                                      ->
  Limit a                                                     ->
  Ordinal b                                                   ->
  (forall c, c :< a -> card (:2: :^^: Aleph!c) :< Aleph!a)    ->
  Aleph!b :< charac (Aleph!a)                                 ->
  card (Aleph!a :^^: Aleph!b) = Aleph!a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1 H2 H3 H4.
  assert (Ordinal a) as G1. { apply H1. }
  assert (Ordinal Aleph!a) as G2. { apply Aleph.IsOrdinal. assumption. }
  assert (Ordinal Aleph!b) as G3. { apply Aleph.IsOrdinal. assumption. }
  assert (Cardinal Aleph!a) as G4. { apply Aleph.IsCardinal. assumption. }
  assert (InfiniteCard Aleph!b) as G5. { apply Aleph.IsInfiniteCard. assumption. }
  remember :[fun c => Aleph!c :^^: Aleph!b]: as F eqn:HF.
  (* The exponent index is below a, because it is below the character.          *)
  assert (b :< a) as H5. {
    assert (Ordinal (charac (Aleph!a))) as K1. { apply Character.IsOrdinal. }
    assert (charac (Aleph!a) :<=: Aleph!a) as K2. {
      apply Character.IsIncl. assumption. }
    assert (Aleph!b :< Aleph!a) as K3. {
      apply Ordinal.ElemInclTran with (charac (Aleph!a)); assumption. }
    apply Aleph.ElemCompatRev; assumption. }
  (* Every member of the indexed family has cardinal below Aleph(a).            *)
  assert (forall c, c :< a -> card (F!c) :<=: card Aleph!a) as H6. {
    intros c H6. rewrite HF, CFF.Eval.
    assert (Ordinal c) as K1. { apply (Ordinal.IsOrdinal a); assumption. }
    assert (Ordinal (card (:2: :^^: Aleph!c))) as K2. { apply Number.IsOrdinal. }
    assert (card (:2: :^^: Aleph!c) :<=: Aleph!a) as K3. {
      apply Ordinal.ElemIsIncl; try assumption. apply H3. assumption. }
    assert (c :< b \/ b :<=: c) as K4. { apply Ordinal.ElemOrIncl; assumption. }
    destruct K4 as [K4|K4].
    - assert (c :<=: b) as K5. { apply Ordinal.ElemIsIncl; assumption. }
      assert (Aleph!c :<=: Aleph!b) as K6. { apply Aleph.InclCompat; assumption. }
      assert (card (Aleph!c :^^: Aleph!b) = card (:2: :^^: Aleph!b)) as K7. {
        apply WhenAlephInclL; assumption. }
      assert (card (:2: :^^: Aleph!b) :<=: Aleph!a) as K8. {
        apply Ordinal.ElemIsIncl; try assumption. apply H3. assumption. }
      rewrite K7. rewrite Aleph.Card; assumption.
    - assert (Aleph!b :<=: Aleph!c) as K5. { apply Aleph.InclCompat; assumption. }
      assert (card (Aleph!c :^^: Aleph!b) :<=: card (:2: :^^: Aleph!c)) as K6. {
        apply WhenAlephInclR; assumption. }
      assert (card (Aleph!c :^^: Aleph!b) :<=: Aleph!a) as K7. {
        apply Incl.Tran with (card (:2: :^^: Aleph!c)); assumption. }
      rewrite Aleph.Card; assumption. }
  (* The union-product estimate bounds the upper side by Aleph(a).              *)
  assert (card (Aleph!a :^^: Aleph!b) :<=: Aleph!a) as H7. {
    assert (Aleph!a :^^: Aleph!b = :\/:_{a} F) as K1. {
      rewrite HF. apply WhenLimitAlephL; assumption. }
    rewrite K1.
    assert (card (:\/:_{a} F) :<=: card (a :x: Aleph!a)) as K3. {
      apply WithChoice.UnionGenProd; assumption. }
    assert (card a :<=: card Aleph!a) as K4. {
      apply WithChoice.InclCompat. 1: assumption. apply Aleph.IsIncl. assumption. }
    assert (card (a :x: Aleph!a) :<=: card (Aleph!a :x: Aleph!a)) as K5. {
      apply WithChoice.InclCompatProdL; assumption. }
    assert (:N :<=: card Aleph!a) as K6. {
      rewrite Aleph.Card. 2: assumption.
      apply InfiniteCard.IsIncl. apply Aleph.IsInfiniteCard. assumption. }
    assert (card (Aleph!a :x: Aleph!a) = card Aleph!a) as K7. {
      apply Number.Square. assumption. }
    assert (card (a :x: Aleph!a) :<=: card Aleph!a) as K8. {
      rewrite <- K7. assumption. }
    assert (card (:\/:_{a} F) :<=: card Aleph!a) as K9. {
      apply Incl.Tran with (card (a :x: Aleph!a)); assumption. }
    rewrite Aleph.Card in K9; assumption. }
  (* Constant functions give the opposite bound.                                *)
  assert (Aleph!a :<=: card (Aleph!a :^^: Aleph!b)) as H8. {
    assert (Aleph!b <> :0:) as K1. { apply InfiniteCard.IsNotZero. assumption. }
    assert (card Aleph!a :<=: card (Aleph!a :^^: Aleph!b)) as K2. {
      apply IsInclCardR; assumption. }
    rewrite Aleph.Card in K2; assumption. }
  apply Incl.Double. split; assumption.
Qed.

(* Every Aleph is below its power by its cofinality character.                  *)
Proposition IsLessCharacL : forall (a:U), Choice -> Ordinal a ->
  Aleph!a :< card (Aleph!a :^^: charac (Aleph!a)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC H1.
  assert (a = :0: \/ Successor a \/ Limit a) as H2. {
    apply Limit.ThreeWay. assumption. }
  destruct H2 as [H2|[H2|H2]].
  - subst.
    (* The zeroth Aleph is regular, so its character is itself.                 *)
    rewrite Regular.WhenZeroCharac.
    (* Cantor gives the strict lower bound by the two-valued power.             *)
    assert (Aleph!:0: :< card (:2: :^^: Aleph!:0:)) as H3. {
      apply CantorAlephCard; assumption. }
    (* The diagonal Aleph power has that same cardinal.                         *)
    assert (card (Aleph!:0: :^^: Aleph!:0:) = card (:2: :^^: Aleph!:0:)) as H4. {
      apply AlephSame; assumption. }
    rewrite H4. assumption.
  - destruct H2 as [b [H2 H3]]. subst.
    assert (Ordinal (succ b)) as G1. { apply Succ.IsOrdinal. assumption. }
    (* A successor-indexed Aleph is regular, so its character is itself.        *)
    rewrite Regular.WhenSuccCharac; try assumption.
    (* Cantor gives the strict lower bound by the two-valued power.             *)
    assert (Aleph!(succ b) :< card (:2: :^^: Aleph!(succ b))) as H3. {
      apply CantorAlephCard; assumption. }
    (* The diagonal Aleph power has that same cardinal.                         *)
    assert (card (Aleph!(succ b) :^^: Aleph!(succ b)) =
      card (:2: :^^: Aleph!(succ b))) as H4. { apply AlephSame; assumption. }
    rewrite H4. assumption.
  - remember (charac (Aleph!a)) as b eqn:Hb.
    assert (Ordinal Aleph!a) as G1. { apply Aleph.IsOrdinal. assumption. }
    assert (Limit Aleph!a) as G2. { apply Aleph.IsLimit. assumption. }
    assert (Cofinal Aleph!a b) as H3. {
      rewrite Hb. apply Character.IsCofinal. assumption. }
    (* The character supplies a cofinal generalized-union representation.       *)
    assert (exists f, Monotone f /\ Fun f b Aleph!a /\ Aleph!a = :\/:_{b} f)
      as H4. { apply Cofinal.UnionGen; assumption. }
    destruct H4 as [f [H4 [H5 H6]]].
    remember (From.from b (fun x => (f!x)^:+:)) as c eqn:Hc.
    (* Each chosen successor-cardinal fibre is larger than the corresponding    *)
    (* cofinal value.                                                           *)
    assert (forall x, x :< b -> card (f!x) :< card (c!x)) as H7. {
      intros x H7. rewrite Hc, From.Eval. 2: assumption.
      apply Successor.IsMoreCard. }
    (* Zermelo's theorem gives the strict lower bound by the product.           *)
    assert (card (:\/:_{b} f) :< card (:prd:_{b} c)) as H8. {
      apply WithChoice.Zermelo; assumption. }
    assert (Aleph!a :< card (:prd:_{b} c)) as H9. {
      assert (card (:\/:_{b} f) = Aleph!a) as K1. {
        rewrite <- H6. apply Aleph.Card. assumption. }
      rewrite K1 in H8. assumption. }
    (* The union of the successor-cardinal fibres is still below Aleph(a).      *)
    assert (:\/:_{b} c :<=: Aleph!a) as H10. {
      intros y H10. apply UnionGen.Charac in H10. destruct H10 as [x [H10 H11]].
      rewrite Hc, From.Eval in H11. 2: assumption.
      assert (f!x :< Aleph!a) as K1. { apply Fun.IsInRange with b; assumption. }
      assert ((f!x)^:+: :< Aleph!a) as K2. {
        apply Successor.IsLessAleph; assumption. }
      assert (Ordinal Aleph!a) as K3. { apply Aleph.IsOrdinal. assumption. }
      apply Ordinal.Charac in K3. destruct K3 as [K3 _].
      apply K3 with ((f!x)^:+:); assumption. }
    (* Product members are maps into the generalized union of the fibres.       *)
    assert (card (:prd:_{b} c) :<=: card ((:\/:_{b} c) :^^: b)) as H11. {
      apply WithChoice.InclCompat. 1: assumption. apply ProdGen.IsIncl. }
    assert (card (:\/:_{b} c) :<=: card Aleph!a) as H12. {
      apply WithChoice.InclCompat; assumption. }
    assert (card ((:\/:_{b} c) :^^: b) :<=: card (Aleph!a :^^: b)) as H13. {
        apply InclCompatCardL; assumption. }
    assert (Aleph!a :< card ((:\/:_{b} c) :^^: b)) as H14. {
      apply Ordinal.ElemInclTran with (card (:prd:_{b} c));
      try assumption; apply Number.IsOrdinal. }
    apply Ordinal.ElemInclTran with (card ((:\/:_{b} c) :^^: b));
    try assumption; apply Number.IsOrdinal.
Qed.

(* Every Aleph exponent is below the character of the resulting cardinal.       *)
Proposition IsLessCharacR : forall (a b:U), Choice -> Ordinal a -> Ordinal b ->
  Aleph!b :< charac (card (Aleph!a :^^: Aleph!b)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1 H2.
  remember (card (Aleph!a :^^: Aleph!b)) as c eqn:Hc.
  assert (InfiniteCard c) as H3. {
    rewrite Hc. apply IsInfiniteCard; try assumption.
    - rewrite Aleph.Card; try assumption.
      apply Aleph.IsInfiniteCard. assumption.
    - apply Aleph.IsNotZero. assumption. }
  assert (Ordinal c) as G1. { apply InfiniteCard.IsOrdinal. assumption. }
  assert (Ordinal (charac c)) as G2. { apply Character.IsOrdinal. }
  assert (Ordinal Aleph!b) as G3. { apply Aleph.IsOrdinal. assumption. }
  assert (Aleph!b :< charac c \/ charac c :<=: Aleph!b) as H4. {
    apply Ordinal.ElemOrIncl; assumption. }
  destruct H4 as [H4|H4]. 1: assumption. exfalso.
  assert (InfiniteCard (charac c)) as H5. {
    apply Character.IsInfiniteCard. assumption. }
  assert (charac c <> :0:) as H6. { apply InfiniteCard.IsNotZero. assumption. }
  assert (exists d, Ordinal d /\ Aleph!d = c) as H7. {
    apply Aleph.HasIndex. assumption. }
  destruct H7 as [d [H7 H8]].
  (* The previous theorem applies after writing c as an Aleph value.            *)
  assert (c :< card (c :^^: charac c)) as H9. {
    assert (Aleph!d :< card (Aleph!d :^^: charac (Aleph!d))) as K1. {
      apply IsLessCharacL; assumption. }
    rewrite H8 in K1. assumption. }
  (* The contradictory assumption bounds the character by the exponent Aleph.   *)
  assert (card (c :^^: charac c) :<=: card (c :^^: Aleph!b)) as H10. {
    assert (card (charac c) :<=: card Aleph!b) as K1. {
      rewrite Character.Card, Aleph.Card; assumption. }
    apply InclCompatCardR; assumption. }
  (* Currying and the infinite square law collapse this upper bound to c.       *)
  assert (card (c :^^: Aleph!b) = c) as H11. {
    assert (card c = card (Aleph!a :^^: Aleph!b)) as K1. {
      rewrite InfiniteCard.Card; assumption. }
    assert (card (c :^^: Aleph!b) =
      card ((Aleph!a :^^: Aleph!b) :^^: Aleph!b)) as K2. {
        apply CompatCardL; assumption. }
    assert (card ((Aleph!a :^^: Aleph!b) :^^: Aleph!b) =
      card (Aleph!a :^^: (Aleph!b :x: Aleph!b))) as K3. { apply AssocCard. }
    assert (card (Aleph!a :^^: (Aleph!b :x: Aleph!b)) =
      card (Aleph!a :^^: Aleph!b)) as K4. {
        apply CompatCardR. 1: assumption.
        apply Number.SquareOrd.
        - apply Aleph.IsOrdinal. assumption.
        - assert (InfiniteCard Aleph!b) as L1. {
            apply Aleph.IsInfiniteCard. assumption. }
          apply InfiniteCard.IsIncl. assumption. }
    rewrite K2, K3, K4. symmetry. assumption. }
  assert (card (c :^^: charac c) :<=: c) as H12. {
    assert (card (c :^^: Aleph!b) :<=: c) as K1. {
      rewrite H11. apply Incl.Refl. }
    apply Incl.Tran with (card (c :^^: Aleph!b)); assumption. }
  assert (c :< c) as H13. {
    apply Ordinal.ElemInclTran with (card (c :^^: charac c));
    try assumption; apply Number.IsOrdinal. }
  revert H13. apply Foundation.NoLoop1.
Qed.

(* Every Aleph is below the character of its two-valued power.                  *)
Proposition Konig : forall (a:U), Choice -> Ordinal a ->
  Aleph!a :< charac (card (:2: :^^: Aleph!a)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC H1.
  assert (card (:N :^^: Aleph!a) = card (:2: :^^: Aleph!a)) as H2. {
    assert (card (Aleph!:0: :^^: Aleph!a) = card (:2: :^^: Aleph!a)) as K1. {
      apply WhenAlephInclL; try assumption.
        - apply Ordinal.Zero.
        - apply Aleph.InclCompat. 2: assumption.
          + apply Ordinal.Zero.
          + apply Empty.IsIncl. }
    rewrite Aleph.WhenZero in K1. assumption. }
  assert (Aleph!a :< charac (card (Aleph!:0: :^^: Aleph!a))) as H3. {
    apply IsLessCharacR; try assumption. apply Ordinal.Zero. }
  rewrite Aleph.WhenZero, H2 in H3. assumption.
Qed.

(* Under GCH, a small Aleph exponent of an Aleph base has the base cardinal.    *)
Proposition WhenGCHL : forall (a b:U),
  Choice                                                      ->
  GCH                                                         ->
  Ordinal a                                                   ->
  Ordinal b                                                   ->
  Aleph!b :< charac (Aleph!a)                                 ->
  card (Aleph!a :^^: Aleph!b) = Aleph!a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC GCH H1 H2 H3.
  assert (a = :0: \/ Successor a \/ Limit a) as H4. {
    apply Limit.ThreeWay. assumption. }
  destruct H4 as [H4|[H4|H4]].
  - subst.
    (* The zeroth Aleph is regular, so its character is itself.                 *)
    rewrite Regular.WhenZeroCharac in H3.
    (* But every Aleph is at least the zeroth one.                              *)
    assert (Aleph!:0: :<=: Aleph!b) as H4. {
      apply Aleph.InclCompat; try assumption. apply Empty.IsIncl. }
    assert (Aleph!b :< Aleph!b) as H5. { apply H4. assumption. }
    exfalso. revert H5. apply Foundation.NoLoop1.
  - destruct H4 as [c [H4 H5]]. subst.
    assert (Ordinal (succ c)) as G1. { apply Succ.IsOrdinal. assumption. }
    assert (Ordinal Aleph!c) as G2. { apply Aleph.IsOrdinal. assumption. }
    assert (Ordinal Aleph!b) as G3. { apply Aleph.IsOrdinal. assumption. }
    (* A successor-indexed Aleph is regular, so the exponent index is earlier.  *)
    assert (b :<=: c) as H6. {
      rewrite Regular.WhenSuccCharac in H3; try assumption.
      assert (b :< succ c) as K1. { apply Aleph.ElemCompatRev; assumption. }
      apply Succ.InclIsElem; assumption. }
    (* GCH identifies the next Aleph with the two-valued power below it.        *)
    assert (card (:2: :^^: Aleph!c) = Aleph!(succ c)) as H5. {
      assert (card :P(Aleph!c) = Aleph!(succ c)) as K1. { apply GCH. assumption. }
      rewrite <- K1. apply WhenTwoCardL. }
    (* The comparable product of the two Alephs has the larger cardinal.        *)
    assert (card (Aleph!c :x: Aleph!b) = Aleph!c) as H7. {
      assert (:N :<=: card Aleph!c) as K1. {
        rewrite Aleph.Card. 2: assumption.
        apply InfiniteCard.IsIncl. apply Aleph.IsInfiniteCard. assumption. }
      assert (:0: :< card Aleph!b) as K2. {
        rewrite Aleph.Card. 2: assumption.
        apply Ordinal.HasZero.
        - apply Aleph.IsOrdinal; assumption.
        - apply Aleph.IsNotZero. assumption. }
      assert (card (Aleph!c :x: Aleph!b) = card Aleph!c :\/: card Aleph!b) as K3. {
        apply Number.ProdMax; assumption. }
      assert (Aleph!b :<=: Aleph!c) as K4. { apply Aleph.InclCompat; assumption. }
      assert (Aleph!c = Aleph!c :\/: Aleph!b) as K5. {
        apply Union2.WhenEqualL. assumption. }
      rewrite K3, Aleph.Card, Aleph.Card; try assumption. symmetry. assumption. }
    (* Currying transports the calculation back to the original power.          *)
    assert (card (Aleph!(succ c) :^^: Aleph!b) =
      card ((:2: :^^: Aleph!c) :^^: Aleph!b)) as H8. {
        apply CompatCardL; try assumption. rewrite Aleph.Card; try assumption.
        symmetry. assumption. }
    assert (card ((:2: :^^: Aleph!c) :^^: Aleph!b) =
      card (:2: :^^: (Aleph!c :x: Aleph!b))) as H9. { apply AssocCard. }
    assert (card (:2: :^^: (Aleph!c :x: Aleph!b)) =
      card (:2: :^^: Aleph!c)) as H10. {
        apply CompatCardR. 1: assumption. rewrite Aleph.Card; assumption. }
    rewrite H8, H9, H10, H5. reflexivity.
  - (* At a limit index, GCH supplies the bound needed by IsAlephBase.          *)
    assert (card (Aleph!a :^^: Aleph!b) = Aleph!a) as H5. {
      assert (forall c, c :< a -> card (:2: :^^: Aleph!c) :< Aleph!a) as K1. {
        intros c K1.
        assert (Ordinal c) as K2. { apply (Ordinal.IsOrdinal a); assumption. }
        assert (Ordinal (succ c)) as K3. { apply Succ.IsOrdinal. assumption. }
        assert (succ c :< a) as K4. { apply Limit.HasSucc; assumption. }
        assert (card (:2: :^^: Aleph!c) = Aleph!(succ c)) as K5. {
          assert (card :P(Aleph!c) = Aleph!(succ c)) as L1. {
            apply GCH. assumption. }
          rewrite <- L1. apply WhenTwoCardL. }
        rewrite K5. apply Aleph.ElemCompat; assumption. }
      apply IsAlephBase; assumption. }
    assumption.
Qed.

(* Under GCH, a middle Aleph exponent of an Aleph base has next cardinal.       *)
Proposition WhenGCHM : forall (a b:U),
  Choice                                                      ->
  GCH                                                         ->
  Ordinal a                                                   ->
  Ordinal b                                                   ->
  charac (Aleph!a) :<=: Aleph!b                               ->
  Aleph!b :<=: Aleph!a                                        ->
  card (Aleph!a :^^: Aleph!b) = Aleph!(succ a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC GCH H1 H2 H3 H4.
  assert (Ordinal Aleph!a) as G1. { apply Aleph.IsOrdinal. assumption. }
  assert (Ordinal Aleph!b) as G2. { apply Aleph.IsOrdinal. assumption. }
  assert (Ordinal (charac (Aleph!a))) as G3. { apply Character.IsOrdinal. }
  assert (Cardinal (card (Aleph!a :^^: Aleph!b))) as G4. {
    exists (Aleph!a :^^: Aleph!b). reflexivity. }
  (* The character power is already above the base Aleph.                       *)
  assert (Aleph!a :< card (Aleph!a :^^: charac (Aleph!a))) as H5. {
    apply IsLessCharacL; assumption. }
  (* Monotonicity in the exponent carries that lower bound to the given power.  *)
  assert (card (Aleph!a :^^: charac (Aleph!a)) :<=:
    card (Aleph!a :^^: Aleph!b)) as H6. {
      assert (InfiniteCard (charac (Aleph!a))) as K1. {
        apply Character.IsInfiniteCard. apply Aleph.IsInfiniteCard. assumption. }
      assert (charac (Aleph!a) <> :0:) as K2. {
        apply InfiniteCard.IsNotZero. assumption. }
      assert (card (charac (Aleph!a)) :<=: card Aleph!b) as K3. {
        rewrite Character.Card, Aleph.Card; assumption. }
      apply InclCompatCardR; assumption. }
  (* Therefore the successor cardinal of the base Aleph is below the power.     *)
  assert (Aleph!(succ a) :<=: card (Aleph!a :^^: Aleph!b)) as H7. {
    assert (Aleph!a :< card (Aleph!a :^^: Aleph!b)) as K1. {
      apply Ordinal.ElemInclTran with (card (Aleph!a :^^: charac (Aleph!a)));
      try assumption; apply Number.IsOrdinal. }
    assert ((Aleph!a)^:+: :<=: card (Aleph!a :^^: Aleph!b)) as K2. {
      apply Successor.IsLowerBoundCard; assumption. }
    rewrite Successor.WhenAleph in K2; assumption. }
  (* The exponent Aleph bound reduces the power to the two-valued diagonal.     *)
  assert (card (Aleph!a :^^: Aleph!b) :<=: Aleph!(succ a)) as H8. {
    assert (card (Aleph!a :^^: Aleph!b) :<=: card (:2: :^^: Aleph!a)) as K2. {
      apply WhenAlephInclR; assumption. }
    assert (card (:2: :^^: Aleph!a) = card :P(Aleph!a)) as K3. {
      apply WhenTwoCardL. }
    assert (card :P(Aleph!a) = Aleph!(succ a)) as K4. { apply GCH. assumption. }
    rewrite K3, K4 in K2. assumption. }
  (* The two inclusions identify the middle-case cardinal exactly.              *)
  apply Incl.Double. split; assumption.
Qed.

