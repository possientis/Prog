Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Choice.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Set.Cardinal.WellOrderable.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.WellOrdering.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Id.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Map.Sum.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Sum.
Require Import ZF.Set.Union.
Require Import ZF.Set.Union2.

Module SCC := ZF.Set.Cardinal.Core.
Module CEM := ZF.Class.Empty.
Module CRC := ZF.Class.Relation.Choice.
Module CRD := ZF.Class.Relation.Domain.
Module CRL := ZF.Class.Relation.Functional.
Module CRO := ZF.Class.Relation.OneToOne.
Module SCW := ZF.Set.Cardinal.WellOrderable.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.
Module SMS := ZF.Set.Relation.Map.Sum.


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
      apply SCW.WithChoice. assumption. }
    destruct H3 as [c H3]. apply CEM.HasElem. exists c. assumption.
  - intros c [H3 H4]. apply H2; assumption.
Qed.

(* Assuming choice, every set is equipotent to its cardinal.                    *)
Proposition IsEquiv : forall (a:U), Choice ->
  a :~: card a.
Proof.
  intros a AC. apply SCC.IsEquiv, SCW.WithChoice. assumption.
Qed.

(* Assuming choice, every set admits an explicit well-ordering relation.        *)
Proposition HasWellOrdering : forall (a:U),
  Choice -> exists r, WellOrdering r a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC.
  (* Choice makes the set well-orderable, then transport gives the relation.    *)
  apply SCW.HasWellOrdering. apply SCW.WithChoice. assumption.
Qed.

(* Assuming choice, two sets are equipotent iff they have the same cardinal.    *)
Proposition EquivCharac : forall (a b:U), Choice ->
  a :~: b <-> card a = card b.
Proof.
  intros a b AC. apply SCC.EquivCharac; apply SCW.WithChoice; assumption.
Qed.

(* Assuming choice, inclusion implies inequality of cardinals.                  *)
Proposition InclCompat : forall (a b:U), Choice ->
  a :<=: b -> card a :<=: card b.
Proof.
  intros a b AC. apply SCC.InclCompat, SCW.WithChoice. assumption.
Qed.

(* Assuming choice, cardinal equality is compatible with products.              *)
Proposition EqualCompatProd : forall (a b c d:U),
  Choice                              ->
  card a = card c                     ->
  card b = card d                     ->
  card (a :x: b) = card (c :x: d).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c d AC H1 H2.
  (* Choice supplies the well-orderability assumptions needed by SCC.           *)
  apply SCC.EqualCompatProd; try assumption; apply SCW.WithChoice; assumption.
Qed.

(* Assuming choice, cardinal equality is compatible with product on the right.  *)
Proposition EqualCompatProdL : forall (a b c:U), Choice ->
  card a = card b -> card (a :x: c) = card (b :x: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* Keep the right factor fixed and use reflexivity on its cardinal.           *)
  apply EqualCompatProd; try assumption. reflexivity.
Qed.

(* Assuming choice, cardinal equality is compatible with product on the left.   *)
Proposition EqualCompatProdR : forall (a b c:U), Choice ->
  card a = card b -> card (c :x: a) = card (c :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* Keep the left factor fixed and use reflexivity on its cardinal.            *)
  apply EqualCompatProd; try assumption. reflexivity.
Qed.

(* Any set whose cardinal is bounded by card(a) is equipotent to a subset of a. *)
Proposition HasSubsetOfSize : forall (a c:U), Choice ->
  c :<=: card a -> exists b, b :<=: a /\ b :~: c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a c AC H1.
  (* Choose a bijection from card(a) onto a, and take the image of c.           *)
  assert (a :~: card a) as H2. { apply IsEquiv. assumption. }
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

(* Assuming choice, the Cantor-Schroeder-Bernstein theorem holds.               *)
Proposition CantorShroderBernstein : forall (a b c d:U),
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
    apply SCW.WithChoice. assumption. }
  destruct H1 as [b [H1 H2]].
  assert (Ordinal (card b)) as G1. { apply SCC.IsOrdinal. }
  assert (Ordinal (card :P(b))) as G2. { apply SCC.IsOrdinal. }
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

(* If b is not empty, then card(a) is bounded by card(a x b).                   *)
Proposition IsInclProdR : forall (a b:U), Choice ->
  b <> :0: -> card a :<=: card (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Choice supplies the well-orderability assumptions needed by SCC.           *)
  apply SCC.IsInclProdR; try assumption; apply SCW.WithChoice; assumption.
Qed.

(* If a is not empty, then card(b) is bounded by card(a x b).                   *)
Proposition IsInclProdL : forall (a b:U), Choice ->
  a <> :0: -> card b :<=: card (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Choice supplies the well-orderability assumptions needed by SCC.           *)
  apply SCC.IsInclProdL; try assumption; apply SCW.WithChoice; assumption.
Qed.

(* Assuming choice, card(a) <= card(b) gives an injection from a into b.        *)
Proposition HasInj : forall (a b:U), Choice ->
  card a :<=: card b -> exists f, Inj f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Choice supplies the well-orderability assumptions needed by SCC.HasInj.    *)
  assert (WellOrderable a) as H2. { apply SCW.WithChoice. assumption. }
  assert (WellOrderable b) as H3. { apply SCW.WithChoice. assumption. }
  apply SCC.HasInj; assumption.
Qed.

(* Assuming choice, card(b) <= card(a) gives a surjection from a onto b.        *)
Proposition HasOnto : forall (a b:U), Choice ->
  b <> :0: -> card b :<=: card a -> exists f, Onto f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1 H2.
  (* Choice supplies the well-orderability assumptions needed by SCC.HasOnto.   *)
  assert (WellOrderable a) as H3. { apply SCW.WithChoice. assumption. }
  assert (WellOrderable b) as H4. { apply SCW.WithChoice. assumption. }
  apply SCC.HasOnto; assumption.
Qed.

(* Assuming choice, select injections from each member of a into b.             *)
Proposition InjSelect : forall (a b:U),
  Choice                                    ->
  (forall x, x :< a -> card x :<=: card b)  ->
  exists f,
    FunctionOn f a                          /\
    forall x, x :< a -> Inj (f!x) x b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  remember (fun z => exists x y, z = :(x,y): /\ Inj y x b) as A eqn:H2.
  (* For each x in a, the cardinal bound gives some injection from x into b.    *)
  assert (forall x, x :< a -> exists y, A :(x,y):) as H3. {
    intros x H3.
    assert (exists y, Inj y x b) as H4. {
      apply HasInj. 1: assumption. apply H1. assumption. }
    destruct H4 as [y H4]. exists y. rewrite H2. exists x, y.
    split. 2: assumption. reflexivity. }
  (* Class choice assembles the injections into one indexing function.          *)
  assert (exists f, FunctionOn f a /\ forall x, x :< a -> A :(x,f!x):) as H4. {
    apply CRC.FunctionOn; assumption. }
  destruct H4 as [f [H4 H5]]. exists f. split. 1: assumption.
  intros x H6.
  assert (A :(x,f!x):) as H7. { apply H5. assumption. }
  rewrite H2 in H7. destruct H7 as [u [v [H7 H8]]].
  apply OrdPair.Equal in H7. destruct H7 as [H7 H9]. subst. assumption.
Qed.

(* Assuming choice, select a member of a containing each union element.         *)
Proposition UnionSelect : forall (a:U), Choice ->
  exists f,
    FunctionOn f :U(a)                            /\
    forall x, x :< :U(a) -> x :< f!x /\ f!x :< a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC.
  remember (fun z => exists x y, z = :(x,y): /\ x :< y /\ y :< a) as A eqn:H1.
  (* Each element of the union lies in at least one member of a.                *)
  assert (forall x, x :< :U(a) -> exists y, A :(x,y):) as H2. {
    intros x H2. apply Union.Charac in H2. destruct H2 as [y [H2 H3]].
    exists y. rewrite H1. exists x, y. split. 2: split; assumption.
    reflexivity. }
  (* Class choice turns these containing sets into a selector function.         *)
  assert (exists f,
    FunctionOn f :U(a)  /\
    forall x, x :< :U(a) -> A :(x,f!x):) as H3. {
      apply CRC.FunctionOn; assumption. }
  destruct H3 as [f [H3 H4]]. exists f. split. 1: assumption.
  intros x H5. assert (A :(x,f!x):) as H6. { apply H4. assumption. }
  rewrite H1 in H6. destruct H6 as [u [v [H6 [H7 H8]]]].
  apply OrdPair.Equal in H6. destruct H6 as [H6 H9]. subst. split; assumption.
Qed.

(* Assuming choice, an injection gives an inequality of cardinals.              *)
Proposition WhenInj : forall (a b f:U), Choice ->
  Inj f a b -> card a :<=: card b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f AC H1.
  (* Choice makes the codomain well-orderable, so the general form applies.     *)
  apply SCC.WhenInj with f. 2: assumption.
  apply SCW.WithChoice. assumption.
Qed.

(* Assuming choice, a surjection gives an inequality of cardinals.              *)
Proposition WhenOnto : forall (f a b:U), Choice ->
  Onto f a b -> card b :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b AC H1.
  (* Choice makes the domain well-orderable, so the general form applies.       *)
  apply SCC.WhenOnto with f. 2: assumption.
  apply SCW.WithChoice. assumption.
Qed.

(* Cardinal product is monotone in its right argument.                          *)
Proposition InclCompatProdR : forall (a b c:U), Choice ->
  card b :<=: card c -> card (a :x: b) :<=: card (a :x: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* Choice supplies the well-orderability assumptions needed by SCC.           *)
  apply SCC.InclCompatProdR; try assumption; apply SCW.WithChoice; assumption.
Qed.

(* Cardinal product is monotone in its left argument.                           *)
Proposition InclCompatProdL : forall (a b c:U), Choice ->
  card a :<=: card b -> card (a :x: c) :<=: card (b :x: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* Choice supplies the well-orderability assumptions needed by SCC.           *)
  apply SCC.InclCompatProdL; try assumption; apply SCW.WithChoice; assumption.
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
Proposition ImageIncl : forall (F:Class) (a:U), Choice ->
  CRL.Functional F -> card F:[a]: :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros F a AC H1.
  (* Choice makes a well-orderable, so the general image bound applies.         *)
  apply SCC.ImageIncl. 2: assumption. apply SCW.WithChoice. assumption.
Qed.

(* The cardinal of a union is bounded by the cardinal of the disjoint sum.      *)
Proposition UnionSum : forall (a b:U), Choice ->
  card (a :\/: b) :<=: card (a :++: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC.
  remember (either a b (id a) (id b)) as f eqn:H1.
  (* The either map from the disjoint sum onto the ordinary union is onto.      *)
  assert (Onto f (a :++: b) (a :\/: b)) as H2. { rewrite H1. apply SMS.HasOnto. }
  (* A surjection bounds the cardinal of its codomain by that of its domain.    *)
  apply WhenOnto with f; assumption.
Qed.

(* The cardinal of a union is bounded by the cardinal of a product.             *)
Proposition UnionProd : forall (a b:U),
  Choice                                      ->
  (forall x, x :< a -> card x :<=: card b)    ->
  card :U(a) :<=: card (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Choose, for each member of a, an injection into b.                         *)
  assert (exists f, FunctionOn f a /\ forall x, x :< a -> Inj (f!x) x b) as H2. {
    apply InjSelect; assumption. }
  destruct H2 as [f [H2 H3]].
  (* Choose, for each element of the union, a member of a containing it.        *)
  assert (exists h, FunctionOn h :U(a) /\
    forall x, x :< :U(a) -> x :< h!x /\ h!x :< a) as H4. {
    apply UnionSelect. assumption. }
  destruct H4 as [h [H4 H5]].
  remember (From.from :U(a) (fun x => :(h!x, (f!(h!x))!x):)) as g eqn:H6.
  (* The displayed map sends each union element into a x b and is injective.    *)
  assert (Inj g :U(a) (a :x: b)) as H7. {
    rewrite H6. apply From.IsInj.
    - intros x H7. assert (x :< h!x /\ h!x :< a) as H8. {
        apply H5. assumption. }
      destruct H8 as [H8 H9]. apply Prod.Charac2. split. 1: assumption.
      assert (Inj (f!(h!x)) (h!x) b) as H10. { apply H3. assumption. }
      apply Inj.IsInRange with (h!x); assumption.
    - intros x y H7 H8 H9.
      assert (x :< h!x /\ h!x :< a) as H10. { apply H5. assumption. }
      assert (y :< h!y /\ h!y :< a) as H11. { apply H5. assumption. }
      destruct H10 as [H10 H12]. destruct H11 as [H11 H13].
      apply OrdPair.Equal in H9. destruct H9 as [H9 H14].
      rewrite <- H9 in H14.
      assert (Inj (f!(h!x)) (h!x) b) as H15. { apply H3. assumption. }
      apply (BijectionOn.EvalInjective (f!(h!x)) (h!x)); try assumption.
      + apply H15.
      + rewrite H9. assumption. }
  (* An injection into the product gives the desired cardinal bound.            *)
  apply WhenInj with g; assumption.
Qed.

