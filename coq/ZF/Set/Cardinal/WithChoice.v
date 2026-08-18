Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Choice.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Set.Cardinal.WellOrderable.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.WellOrdering.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.ProdGen.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Id.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Map.Sum.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Sum.
Require Import ZF.Set.Union.
Require Import ZF.Set.Union2.
Require Import ZF.Set.UnionGen.

Module CEM := ZF.Class.Empty.
Module CRD := ZF.Class.Relation.Domain.
Module CFF := ZF.Class.Relation.Fun.From.
Module CRL := ZF.Class.Relation.Functional.


(* The cardinal of a set is the largest such lower bound.                       *)
Proposition IsLargest : forall (a b:U),
  Choice                                        ->
  Ordinal b                                     ->
  (forall c, Ordinal c -> a :~: c -> b :<=: c)  ->
  b :<=: card a.
Proof.
  intros a b AC H1 H2.
  apply InfOfClass.IsLargest.
  - intros c H3. apply H3.
  - assert (exists c, Ordinal c /\ a :~: c) as H3. {
      apply WellOrderable.WithChoice. assumption. }
    destruct H3 as [c H3]. apply CEM.HasElem. exists c. assumption.
  - intros c [H3 H4]. apply H2; assumption.
Qed.

(* Assuming choice, every set is equipotent to its cardinal.                    *)
Proposition IsEquip : forall (a:U), Choice ->
  a :~: card a.
Proof.
  intros a AC. apply Number.IsEquip, WellOrderable.WithChoice. assumption.
Qed.

(* Assuming choice, every set admits an explicit well-ordering relation.        *)
Proposition HasWellOrdering : forall (a:U),
  Choice -> exists r, WellOrdering r a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC.
  (* Choice makes the set well-orderable, then transport gives the relation.    *)
  apply WellOrderable.HasWellOrdering.
  apply WellOrderable.WithChoice. assumption.
Qed.

(* Assuming choice, two sets are equipotent iff they have the same cardinal.    *)
Proposition EquipCharac : forall (a b:U), Choice ->
  a :~: b <-> card a = card b.
Proof.
  intros a b AC.
  apply Number.EquipCharac; apply WellOrderable.WithChoice; assumption.
Qed.

(* Assuming choice, inclusion implies inequality of cardinals.                  *)
Proposition InclCompat : forall (a b:U), Choice ->
  a :<=: b -> card a :<=: card b.
Proof.
  intros a b AC. apply Number.InclCompat, WellOrderable.WithChoice. assumption.
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
  (* Choice supplies the well-orderability assumptions needed by Number.        *)
  apply Number.EqualCompatProd; try assumption;
  apply WellOrderable.WithChoice; assumption.
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
  assert (a :~: card a) as H2. { apply IsEquip. assumption. }
  apply Equip.Sym in H2. destruct H2 as [f H2].
  exists f:[c]:. split.
  - (* Since c is contained in card(a), its image is contained in a.            *)
    intros y H3. apply (Bij.ImageCharac f (card a) a c) in H3. 2: assumption.
    destruct H3 as [x [H3 [H4 H5]]]. rewrite <- H5.
    apply Bij.IsInRange with (card a); assumption.
  - (* Restricting the bijection to c bijects c onto its image.                 *)
    apply Equip.Sym. exists (f:|:c).
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
  assert (card a = card c) as H5. { apply EquipCharac; assumption. }
  assert (card b = card d) as H6. { apply EquipCharac; assumption. }
  assert (card c :<=: card b) as H7. { apply InclCompat; assumption. }
  assert (card d :<=: card a) as H8. { apply InclCompat; assumption. }
  apply EquipCharac. assumption. apply Incl.Double. split.
  - rewrite H5. assumption.
  - rewrite H6. assumption.
Qed.

(* Assuming choice, the cardinal of a is strictly smaller than card(P(a)).      *)
Proposition Cantor : forall (a:U), Choice ->
  card a :< card :P(a).
Proof.
  intros a AC.
  assert (exists b, Ordinal b /\ a :~: b) as H1. {
    apply WellOrderable.WithChoice. assumption. }
  destruct H1 as [b [H1 H2]].
  assert (Ordinal (card b)) as G1. { apply Number.IsOrdinal. }
  assert (Ordinal (card :P(b))) as G2. { apply Number.IsOrdinal. }
  assert (card a = card b) as H3. { apply EquipCharac; assumption. }
  assert (card :P(a) = card :P(b)) as H4. {
    apply EquipCharac, Equip.PowerCompat; assumption. }
  assert (card b :< card :P(b)) as H5. {
    assert (b :<=: :P(b)) as H5. {
      intros c H5.
      assert (Ordinal c) as K1. { apply Ordinal.IsOrdinal with b; assumption. }
      apply Power.Charac. intros d H6.
      assert (Ordinal d) as K2. { apply Ordinal.IsOrdinal with c; assumption. }
      apply Ordinal.ElemElemTran with c; assumption. }
  assert (card b :<=: card :P(b)) as H6. { apply InclCompat; assumption. }
  assert (card b = card :P(b) \/ card b :< card :P(b)) as H7. {
    apply Ordinal.EqualOrElem; assumption. }
  destruct H7 as [H7|H7]. 2:assumption. exfalso.
  assert (b :~: :P(b)) as H8. { apply EquipCharac; assumption. }
  apply Equip.Cantor with b. assumption. }
  rewrite H3, H4. assumption.
Qed.

(* If b is not empty, then card(a) is bounded by card(a x b).                   *)
Proposition IsInclProdR : forall (a b:U), Choice ->
  b <> :0: -> card a :<=: card (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Choice supplies the well-orderability assumptions needed by Number.        *)
  apply Number.IsInclProdR; try assumption;
  apply WellOrderable.WithChoice; assumption.
Qed.

(* If a is not empty, then card(b) is bounded by card(a x b).                   *)
Proposition IsInclProdL : forall (a b:U), Choice ->
  a <> :0: -> card b :<=: card (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Choice supplies the well-orderability assumptions needed by Number.        *)
  apply Number.IsInclProdL; try assumption;
    apply WellOrderable.WithChoice; assumption.
Qed.

(* Assuming choice, card(a) <= card(b) gives an injection from a into b.        *)
Proposition HasInj : forall (a b:U), Choice ->
  card a :<=: card b -> exists f, Inj f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1.
  (* Choice supplies the well-orderability assumptions needed by Number.HasInj. *)
  assert (WellOrderable a) as H2. {
    apply WellOrderable.WithChoice. assumption. }
  assert (WellOrderable b) as H3. {
    apply WellOrderable.WithChoice. assumption. }
  apply Number.HasInj; assumption.
Qed.

(* Assuming choice, card(b) <= card(a) gives a surjection from a onto b.        *)
Proposition HasOnto : forall (a b:U), Choice ->
  b <> :0: -> card b :<=: card a -> exists f, Onto f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC H1 H2.
  (* Choice supplies the well-orderability assumptions needed by Number.HasOnto.*)
  assert (WellOrderable a) as H3. {
    apply WellOrderable.WithChoice. assumption. }
  assert (WellOrderable b) as H4. {
    apply WellOrderable.WithChoice. assumption. }
  apply Number.HasOnto; assumption.
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
    apply Choice.FunctionOn; assumption. }
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
      apply Choice.FunctionOn; assumption. }
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
  apply Number.WhenInj with f. 2: assumption.
  apply WellOrderable.WithChoice. assumption.
Qed.

(* Assuming choice, a surjection gives an inequality of cardinals.              *)
Proposition WhenOnto : forall (f a b:U), Choice ->
  Onto f a b -> card b :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b AC H1.
  (* Choice makes the domain well-orderable, so the general form applies.       *)
  apply Number.WhenOnto with f. 2: assumption.
  apply WellOrderable.WithChoice. assumption.
Qed.

(* Cardinal product is monotone in its right argument.                          *)
Proposition InclCompatProdR : forall (a b c:U), Choice ->
  card b :<=: card c -> card (a :x: b) :<=: card (a :x: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* Choice supplies the well-orderability assumptions needed by Number.        *)
  apply Number.InclCompatProdR; try assumption;
    apply WellOrderable.WithChoice; assumption.
Qed.

(* Cardinal product is monotone in its left argument.                           *)
Proposition InclCompatProdL : forall (a b c:U), Choice ->
  card a :<=: card b -> card (a :x: c) :<=: card (b :x: c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* Choice supplies the well-orderability assumptions needed by Number.        *)
  apply Number.InclCompatProdL; try assumption;
    apply WellOrderable.WithChoice; assumption.
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
  apply Number.ImageIncl. 2: assumption.
  apply WellOrderable.WithChoice. assumption.
Qed.

(* The cardinal of a union is bounded by the cardinal of the disjoint sum.      *)
Proposition UnionSum : forall (a b:U), Choice ->
  card (a :\/: b) :<=: card (a :++: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b AC.
  remember (either a b (id a) (id b)) as f eqn:H1.
  (* The either map from the disjoint sum onto the ordinary union is onto.      *)
  assert (Onto f (a :++: b) (a :\/: b)) as H2. { rewrite H1. apply Sum.HasOnto. }
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

(* The cardinal of the union of an image is bounded by a product.               *)
Proposition UnionProdImage : forall (F:Class) (a b:U),
  Choice                                          ->
  Functional F                                    ->
  (forall x, x :< a -> card (F!x) :<=: card b)    ->
  card :U(F:[a]:) :<=: card (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros F a b AC H1 H2.
  (* Every member of the image has cardinal bounded by b.                       *)
  assert (forall y, y :< F:[a]: -> card y :<=: card b) as H3. {
    intros y H3.
    (* Such a member is a value F!x for some x in a.                            *)
    assert (exists x, x :< a /\ F :(x,y):) as H4. {
      apply ImageUnderClass.Charac; assumption. }
    destruct H4 as [x [H4 H5]].
    assert (CRD.domain F x) as H6. { exists y. assumption. }
    assert (F!x = y) as H7. {
      apply EvalOfClass.Charac; assumption. }
    rewrite <- H7. apply H2. assumption. }
  (* First bound the union of the image by its own index product.               *)
  assert (card :U(F:[a]:) :<=: card (F:[a]: :x: b)) as H4. {
    apply UnionProd; assumption. }
  (* The image index set has cardinal at most the original index set.           *)
  assert (card F:[a]: :<=: card a) as H5. { apply ImageIncl; assumption. }
  assert (card (F:[a]: :x: b) :<=: card (a :x: b)) as H6. {
    apply InclCompatProdL; assumption. }
  apply Incl.Tran with (card (F:[a]: :x: b)); assumption.
Qed.

(* Zermelo's theorem bounds a generalized union by a product.                   *)
Proposition Zermelo : forall (a b c:U),
  Choice                                            ->
  (forall x, x :< a -> card (b!x) :< card (c!x))    ->
  card (:\/:_{a} b) :< card (:prd:_{a} c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c AC H1.
  (* Every c-fibre is non-empty, because a smaller cardinal lies below it.      *)
  assert (forall x, x :< a -> c!x <> :0:) as H2. {
    intros x H2 H3.
    assert (card (b!x) :< card (c!x)) as H4. { apply H1. assumption. }
    assert (card (c!x) = :0:) as H5. {
      rewrite H3. apply Number.WhenNat. apply Omega.HasZero. }
    rewrite H5 in H4. apply Empty.Charac in H4. contradiction. }
  (* Hence the product has at least one member.                                 *)
  assert (:prd:_{a} c <> :0:) as H3. {
    apply Empty.HasElem. apply ProdGen.HasElem; assumption. }
  (* If the desired strict inequality fails, there is a reverse surjection.     *)
  assert (card (:\/:_{a} b) :< card (:prd:_{a} c) \/
    card (:prd:_{a} c) :<=: card (:\/:_{a} b)) as H4. {
    apply Ordinal.ElemOrIncl; apply Number.IsOrdinal. }
  destruct H4 as [H4|H4]. 1: assumption. exfalso.
  assert (exists f, Onto f (:\/:_{a} b) (:prd:_{a} c)) as H5. {
    apply HasOnto; assumption. }
  destruct H5 as [f H5].
  remember (fun x z => (f!z)!x) as D eqn:HD.
  remember (fun x => (From.from (b!x) (D x)) :[ b!x ]:) as d eqn:H6.
  (* The used x-coordinates form a subset of the x-th c-fibre.                  *)
  assert (forall x, x :< a -> d x :<=: c!x) as H7. {
    intros x H7 y H8.
    remember (From.from (b!x) (D x)) as h eqn:H9.
    assert (FunctionOn h (b!x)) as H10. { rewrite H9. apply From.IsFunctionOn. }
    rewrite H6 in H8. rewrite <- H9 in H8.
    apply (FunctionOn.ImageCharac h (b!x) (b!x)) in H8. 2: assumption.
    destruct H8 as [z [H8 [_ H11]]]. rewrite H9 in H11.
    rewrite From.Eval in H11. 2: assumption. rewrite HD in H11.
    rewrite <- H11.
    assert (z :< :\/:_{a} b) as H12. {
      apply UnionGen.Charac. exists x. split; assumption. }
    assert (f!z :< :prd:_{a} c) as H13. {
      apply Onto.IsInRange with (:\/:_{a} b); assumption. }
    apply ProdGen.EvalIsIn with a; assumption. }
  (* Each used-coordinate set is no larger than the corresponding b-fibre.      *)
  assert (forall x, x :< a -> card (d x) :<=: card (b!x)) as H8. {
    intros x H8.
    remember (From.from (b!x) (D x)) as h eqn:H9.
    assert (FunctionOn h (b!x)) as H10. { rewrite H9. apply From.IsFunctionOn. }
    assert (Onto h (b!x) (d x)) as H11. {
      split. 1: assumption. rewrite H6. rewrite <- H9.
      symmetry. apply FunctionOn.ImageOfDomain. assumption. }
    apply WhenOnto with h; assumption. }
  (* Therefore each complement c(x) \ d(x) is non-empty.                        *)
  assert (forall x, x :< a -> c!x :\: d x <> :0:) as H9. {
    intros x H9.
    assert (card (d x) :< card (c!x)) as H10. {
      apply Ordinal.InclElemTran with (card (b!x)).
      1-3: apply Number.IsOrdinal.
      - apply H8. assumption.
      - apply H1. assumption. }
    intros H11. apply Diff.WhenZero in H11.
    assert (d x = c!x) as H12. {
      apply Incl.Double. split. 1: apply H7. assumption. assumption. }
    assert (card (d x) = card (c!x)) as H13. { rewrite H12. reflexivity. }
    rewrite H13 in H10. revert H10. apply Foundation.NoLoop1. }
  (* Choice selects a diagonal member outside every used-coordinate set.        *)
  assert (exists e, e :< :prd:_{a} (:[fun x => c!x :\: d x]:)) as H10. {
    apply ProdGenOfClass.HasElem. 1: assumption.
    intros x H10. rewrite CFF.Eval. apply H9. assumption. }
  destruct H10 as [e H10].
  assert (e :< :prd:_{a} c) as H11. {
    apply ProdGen.IsIn.
    - apply ProdGenOfClass.IsFunctionOn with (:[fun x => c!x :\: d x]:).
      assumption.
    - intros x H11.
      assert (e!x :< (:[fun x => c!x :\: d x]:)!x) as H12. {
        apply ProdGenOfClass.EvalIsIn with a; assumption. }
      rewrite CFF.Eval in H12. apply Diff.IsIncl in H12. assumption. }
  (* Surjectivity puts the diagonal member somewhere in the alleged list.       *)
  assert (exists z, z :< :\/:_{a} b /\ f!z = e) as H12. {
    assert (e :< :prd:_{a} c <->
      exists z, z :< :\/:_{a} b /\ f!z = e) as H12. {
      apply Onto.RangeCharac. assumption. }
    apply H12. assumption. }
  destruct H12 as [z [H12 H13]]. apply UnionGen.Charac in H12.
  destruct H12 as [x [H12 H14]].
  (* At that fibre, the diagonal value is both used and deliberately unused.    *)
  assert (e!x :< d x) as H15. {
    remember (From.from (b!x) (D x)) as h eqn:H15.
    assert (D x z :< d x) as H16. {
      rewrite H6. rewrite <- H15. apply Image.Charac. exists z.
      split. 1: assumption. rewrite H15. apply From.Satisfies. assumption. }
    rewrite HD in H16. rewrite H13 in H16. assumption. }
  assert (e!x :< (:[fun x => c!x :\: d x]:)!x) as H16. {
    apply ProdGenOfClass.EvalIsIn with a; assumption. }
  rewrite CFF.Eval in H16. apply Diff.Charac in H16.
  destruct H16 as [_ H16]. contradiction.
Qed.

