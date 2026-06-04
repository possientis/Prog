Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Cardinal.WellOrderable.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Id.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Map.Sum.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Sum.
Require Import ZF.Set.Union2.

Module SCC := ZF.Set.Cardinal.Core.
Module CEM := ZF.Class.Empty.
Module CRL := ZF.Class.Relation.Functional.
Module SCW := ZF.Set.Cardinal.WellOrderable.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.
Module SRD := ZF.Set.Relation.Domain.
Module SRR := ZF.Set.Relation.Range.
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


(* Assuming choice, two sets are equipotent iff they have the same cardinal.    *)
Proposition EquivCharac : forall (a b:U), Choice ->
  a :~: b <-> card a = card b.
Proof.
  intros a b AC. split; intros H1.
  - apply SCC.WhenEquiv. assumption.
  - apply Equiv.Tran with (card a).
    + apply IsEquiv. assumption.
    + rewrite H1. apply Equiv.Sym, IsEquiv. assumption.
Qed.


(* Assuming choice, inclusion implies inequality of cardinals.                  *)
Proposition InclCompat : forall (a b:U), Choice ->
  a :<=: b -> card a :<=: card b.
Proof.
  intros a b AC. apply SCC.InclCompat, SCW.WithChoice. assumption.
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
  assert (card a = card f:[a]:) as H5. { apply SCC.WhenEquiv. assumption. }
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
  rewrite SCC.ProdComm. apply IsInclProdR; assumption.
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
  rewrite (SCC.ProdComm a c), (SCC.ProdComm b c).
  apply InclCompatProdR; assumption.
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

