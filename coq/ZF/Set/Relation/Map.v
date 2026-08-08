Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Specify.

Require Import ZF.Notation.Eval.

(* The set of all maps from a to b.                                             *)
Definition map (a b:U) : U := {{ f :< :P(a :x: b) | fun f => Fun f a b }}.

(* The set of all surjections from a onto b.                                    *)
Definition onto (a b:U) : U := {{ f :< map a b | fun f => Onto f a b }}.

(* The set of all injections from a to b.                                       *)
Definition inj (a b:U) : U := {{ f :< map a b | fun f => Inj f a b }}.

(* The set of all bijections from a to b.                                       *)
Definition bij (a b:U) : U := {{ f :< map a b | fun f => Bij f a b }}.

(* A set belongs to map(a,b) iff it is a map from a to b.                       *)
Proposition CharacMap : forall (f a b:U),
  f :< map a b <-> Fun f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [_ H1]. assumption.
  - apply Specify.Charac. split. 2: assumption.
    apply Power.Charac. apply Prod.IsInclFun. assumption.
Qed.

(* A set belongs to onto(a,b) iff it is a surjection from a onto b.             *)
Proposition CharacOnto : forall (f a b:U),
  f :< onto a b <-> Onto f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [_ H1]. assumption.
  - apply Specify.Charac. split. 2: assumption.
    apply CharacMap. apply Onto.IsFun. assumption.
Qed.

(* A set belongs to inj(a,b) iff it is an injection from a to b.                *)
Proposition CharacInj : forall (f a b:U),
  f :< inj a b <-> Inj f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [_ H1]. assumption.
  - apply Specify.Charac. split. 2: assumption.
    apply CharacMap. apply Inj.IsFun. assumption.
Qed.

(* A set belongs to bij(a,b) iff it is a bijection from a to b.                 *)
Proposition CharacBij : forall (f a b:U),
  f :< bij a b <-> Bij f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [_ H1]. assumption.
  - apply Specify.Charac. split. 2: assumption.
    apply CharacMap. apply Bij.IsFun. assumption.
Qed.

(* The set of maps from a to b is included in the power set of a x b.           *)
Proposition IsInclPower : forall (a b:U),
  map a b :<=: :P(a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1. apply Specify.Charac in H1. apply H1.
Qed.

(* The set of surjections from a onto b is included in the set of maps.         *)
Proposition IsInclOnto : forall (a b:U),
  onto a b :<=: map a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1. apply Specify.Charac in H1. apply H1.
Qed.

(* The set of injections from a to b is included in the set of maps.            *)
Proposition IsInclInj : forall (a b:U),
  inj a b :<=: map a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1. apply Specify.Charac in H1. apply H1.
Qed.

(* An injection of codomains induces an injection of map sets.                  *)
Proposition HasInjR : forall (a b c f:U),
  Inj f a b -> exists h, Inj h (map c a) (map c b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f H1.
  (* Post-compose every map c -> a with the fixed injection a -> b.             *)
  remember (From.from (map c a) (fun g => f :.: g)) as h eqn:H2.
  assert (Inj h (map c a) (map c b)) as H3. {
    rewrite H2. apply From.IsInj.
    - (* The post-composite is a map from c into b.                             *)
      intros g H3. apply CharacMap.
      assert (Fun g c a) as H4. { apply CharacMap. assumption. }
      apply Fun.Compose with a. 1: assumption. apply Inj.IsFun. assumption.
    - (* Equal composites have equal original values by injectivity.            *)
      intros g k H3 H4 H5.
      assert (Fun g c a) as H6. { apply CharacMap. assumption. }
      assert (Fun k c a) as H7. { apply CharacMap. assumption. }
      apply Fun.Equal with c a c a; try assumption; try reflexivity.
      intros x H8.
      assert ((f :.: g)!x = (f :.: k)!x) as H9. {
        rewrite H5. reflexivity. }
      assert ((f :.: g)!x = (f!(g!x))) as H10. {
        apply (Fun.ComposeEval g f c a b x); try assumption.
        apply Inj.IsFun. assumption. }
      assert ((f :.: k)!x = f!(k!x)) as H11. {
        apply (Fun.ComposeEval k f c a b x); try assumption.
        apply Inj.IsFun. assumption. }
      rewrite H10, H11 in H9.
      assert (g!x :< a) as H12. { apply Fun.IsInRange with c; assumption. }
      assert (k!x :< a) as H13. { apply Fun.IsInRange with c; assumption. }
      apply (Inj.EvalInjective f a b); assumption. }
  exists h. assumption.
Qed.

(* The set of bijections from a to b is included in the set of maps.            *)
Proposition IsInclBij : forall (a b:U),
  bij a b :<=: map a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1. apply Specify.Charac in H1. apply H1.
Qed.

(* The set of bijections from a to b is included in the set of surjections.     *)
Proposition IsInclBijOnto : forall (a b:U),
  bij a b :<=: onto a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1.
  apply CharacOnto. apply Bij.IsOnto. apply CharacBij. assumption.
Qed.

(* The set of bijections from a to b is included in the set of injections.      *)
Proposition IsInclBijInj : forall (a b:U),
  bij a b :<=: inj a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1.
  apply CharacInj. apply Bij.IsInj. apply CharacBij. assumption.
Qed.
