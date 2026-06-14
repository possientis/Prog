Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Map.

Module SCE := ZF.Set.Cardinal.Equiv.

(* The set of maps is compatible with equipotence of codomains.                 *)
Proposition CompatR : forall (a b c:U),
  a :~: b -> map c a :~: map c b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c [f H1].
  remember (fun h => f :.: h) as q eqn:H2.
  remember (from (map c a) q) as p eqn:H3.
  (* A map c -> a is sent to the composite c -> a -> b.                         *)
  assert (forall h, h :< map c a -> q h :< map c b) as H4. {
    intros h H4. rewrite H2. apply CharacMap.
    assert (Fun h c a) as H5. { apply CharacMap. assumption. }
    apply Fun.Compose with a. 1: assumption. apply Bij.IsFun. assumption. }
  (* Equal composites have equal original maps, since f is injective.           *)
  assert (forall h k,
    h :< map c a -> k :< map c a -> q h = q k -> h = k) as H5. {
    intros h k H5 H6 H7. rewrite H2 in H7.
    assert (Fun h c a) as H8. { apply CharacMap. assumption. }
    assert (Fun k c a) as H9. { apply CharacMap. assumption. }
    assert (Fun f a b) as G1. { apply Bij.IsFun. assumption. }
    apply Fun.Equal with c a c a; try assumption. 1: reflexivity.
    intros x H10.
    assert ((f :.: h)!x = (f :.: k)!x) as H11. { rewrite H7. reflexivity. }
    assert ((f :.: h)!x = f!(h!x)) as G2. {
      apply (Fun.ComposeEval h f c a b x); assumption. }
    assert ((f :.: k)!x = f!(k!x)) as G3. {
      apply (Fun.ComposeEval k f c a b x); assumption. }
    rewrite G2 in H11. rewrite G3 in H11.
    assert ((h!x) :< a) as H12. { apply Fun.IsInRange with c; assumption. }
    assert ((k!x) :< a) as H13. { apply Fun.IsInRange with c; assumption. }
    apply (Bij.EvalInjective f a b (h!x) (k!x)) in H11; assumption. }
  (* A map c -> b is pulled back through the inverse of f.                      *)
  assert (forall k,
    k :< map c b -> exists h, h :< map c a /\ q h = k) as H6. {
    intros k H6.
    remember (f^:-1: :.: k) as h eqn:H7.
    assert (Fun k c b) as H8. { apply CharacMap. assumption. }
    assert (Fun f^:-1: b a) as H9. { apply Bij.IsFun, Bij.Converse. assumption. }
    assert (Fun h c a) as H10. { rewrite H7. apply Fun.Compose with b; assumption. }
    assert (h :< map c a) as H11. { apply CharacMap. assumption. }
    assert (q h = k) as H12. {
      apply Fun.Equal with c b c b; try assumption. 2: reflexivity.
      + apply CharacMap. apply H4. apply CharacMap. assumption.
      + intros x H13. rewrite H2.
      assert (Fun f a b) as G1. { apply Bij.IsFun. assumption. }
      assert ((f :.: h)!x = f!(h!x)) as G2. {
        apply (Fun.ComposeEval h f c a b x); assumption. }
      rewrite G2, H7.
      assert ((f^:-1: :.: k)!x = f^:-1:!(k!x)) as G3. {
        apply (Fun.ComposeEval k f^:-1: c b a x); assumption. }
      rewrite G3.
      assert ((k!x) :< b) as H14. { apply Fun.IsInRange with c; assumption. }
      apply (Bij.EvalOfConverseEval f a b (k!x)); assumption. }
    exists h. split; assumption. }
  exists p. rewrite H3. apply From.IsBij; assumption.
Qed.

(* The set of maps is compatible with equipotence of domains.                   *)
Proposition CompatL : forall (a b c:U),
  a :~: b -> map a c :~: map b c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c [g H1].
  remember (fun h => h :.: g^:-1:) as q eqn:H2.
  remember (from (map a c) q) as p eqn:H3.
  (* A map a -> c is sent to the composite b -> a -> c.                         *)
  assert (forall h, h :< map a c -> q h :< map b c) as H4. {
    intros h H4. rewrite H2. apply CharacMap.
    assert (Fun h a c) as H5. { apply CharacMap. assumption. }
    assert (Fun g^:-1: b a) as H6. {
      apply Bij.IsFun, Bij.Converse. assumption. }
    apply Fun.Compose with a; assumption. }
  (* Equal composites have equal original maps, because g is onto b.            *)
  assert (forall h k, h
    :< map a c -> k :< map a c -> q h = q k -> h = k) as H5. {
    intros h k H5 H6 H7. rewrite H2 in H7.
    assert (Fun h a c) as H8. { apply CharacMap. assumption. }
    assert (Fun k a c) as H9. { apply CharacMap. assumption. }
    apply Fun.Equal with a c a c; try assumption. 1: reflexivity.
    intros x H10.
    assert ((g!x) :< b) as H11. { apply Bij.IsInRange with a; assumption. }
    assert ((g^:-1:)!(g!x) = x) as H12. {
      apply (Bij.ConverseEvalOfEval g a b x); assumption. }
    assert ((h :.: g^:-1:)!(g!x) = (k :.: g^:-1:)!(g!x)) as H13. {
      rewrite H7. reflexivity. }
    assert (Fun g^:-1: b a) as H14. {
      apply Bij.IsFun, Bij.Converse. assumption. }
    assert ((h :.: g^:-1:)!(g!x) = h!((g^:-1:)!(g!x))) as G1. {
      apply (Fun.ComposeEval g^:-1: h b a c (g!x)); assumption. }
    assert ((k :.: g^:-1:)!(g!x) = k!((g^:-1:)!(g!x))) as G2. {
      apply (Fun.ComposeEval g^:-1: k b a c (g!x)); assumption. }
    rewrite G1 in H13. rewrite G2 in H13.
    rewrite H12 in H13. assumption. }
  (* A map b -> c is pulled back by composing with g.                           *)
  assert (forall k,
    k :< map b c -> exists h, h :< map a c /\ q h = k) as H6. {
    intros k H6.
    remember (k :.: g) as h eqn:H7.
    assert (Fun k b c) as H8. { apply CharacMap. assumption. }
    assert (Fun g a b) as H9. { apply Bij.IsFun. assumption. }
    assert (Fun h a c) as H10. {
      rewrite H7. apply Fun.Compose with b; assumption. }
    assert (h :< map a c) as H11. { apply CharacMap. assumption. }
    assert (q h = k) as H12. {
      apply Fun.Equal with b c b c; try assumption. 2: reflexivity.
      + apply CharacMap. apply H4. apply CharacMap. assumption.
      + intros y H13. rewrite H2.
      assert (((g^:-1:)!y) :< a) as H14. {
        apply (Bij.ConverseEvalIsInDomain g a b y); assumption. }
      assert (g!((g^:-1:)!y) = y) as H15. {
        apply (Bij.EvalOfConverseEval g a b y); assumption. }
      assert (Fun g^:-1: b a) as G1. {
        apply Bij.IsFun, Bij.Converse. assumption. }
      assert ((h :.: g^:-1:)!y = h!((g^:-1:)!y)) as G2. {
        apply (Fun.ComposeEval g^:-1: h b a c y); assumption. }
      rewrite G2.
      rewrite H7.
      assert ((k :.: g)!((g^:-1:)!y) = k!(g!((g^:-1:)!y))) as G3. {
        apply (Fun.ComposeEval g k a b c ((g^:-1:)!y)); assumption. }
      rewrite G3.
      rewrite H15. reflexivity. }
    exists h. split; assumption. }
  exists p. rewrite H3. apply From.IsBij; assumption.
Qed.

(* The set of maps is compatible with equipotence in both arguments.            *)
Proposition Compat : forall (a b c d:U),
  a :~: c -> b :~: d -> map a b :~: map c d.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c d H1 H2.
  (* First change the codomain, then change the domain.                         *)
  apply SCE.Tran with (map a d).
  - apply CompatR. assumption.
  - apply CompatL. assumption.
Qed.
