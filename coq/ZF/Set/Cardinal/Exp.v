Require Import ZF.Axiom.Choice.
Require Import ZF.Set.Cardinal.Equip.
Require Import ZF.Set.Cardinal.Map.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Cardinal.WithChoice.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
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

(* The set of maps from a into two is equipotent to the power set of a.         *)
Proposition OfTwo : forall (a:U),
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

(* Exponentiation is left-monotone in cardinal under choice.                    *)
Proposition InclCompatL : forall (a b c:U),
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
Proposition InclCompatR : forall (a b c:U),
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
