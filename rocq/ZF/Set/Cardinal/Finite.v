Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Classic.
Require Import ZF.Set.Core.
Require Import ZF.Set.Cardinal.WithChoice.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Cardinal.Equip.
Require Import ZF.Set.Cardinal.WellOrderable.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.


(* A set is finite if and only if it is equipotent to a natural number.         *)
Definition Finite (a:U) : Prop := exists n, n :< :N /\ a :~: n.

(* Finiteness is preserved under equipotence.                                   *)
Proposition EquipCompat : forall (a b:U),
  a :~: b -> Finite a -> Finite b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* a is finite so a ~ n for some n in N. Since a ~ b, b ~ a ~ n.              *)
  intros a b H1 [n [H2 H3]]. exists n. split. 1: assumption.
  apply Equip.Tran with a. 2: assumption.
  apply Equip.Sym. assumption.
Qed.

Proposition InclCompat : forall (a b:U),
  a :<=: b -> Finite b -> Finite a.
Proof.
  intros a b H1 [n [H2 [f H3]]].
  assert (Ordinal n) as G1. { apply Omega.HasOrdinals. assumption. }
  assert (Ordinal :N) as G2. { apply Omega.IsOrdinal. }
  assert (a :~: f:[a]:) as H4. {
    exists (f:|:a). apply Bij.Restrict with b n; assumption. }
  assert (f:[a]: :<=: n) as H5. {
    intros y H5. apply (Bij.ImageCharac f b n) in H5. 2: assumption.
    destruct H5 as [x [H5 [H6 H7]]]. rewrite <- H7.
    apply Bij.IsInRange with b; assumption. }
  assert (exists m, Ordinal m /\ m :<=: n /\ f:[a]: :~: m) as H8. {
    apply Equip.OrdinalSubset; assumption. }
  destruct H8 as [m [H8 [H9 H10]]].
  assert (m :< :N) as H11. { apply Ordinal.InclElemTran with n; assumption. }
  assert (a :~: m) as H12. { apply Equip.Tran with f:[a]:; assumption. }
  exists m; split; assumption.
Qed.

Proposition WhenNat : forall (n:U), n :< :N -> Finite n.
Proof.
  intros n H1. exists n. split. 1: assumption. apply Equip.Refl.
Qed.

(* The empty set is finite.                                                     *)
Proposition Zero : Finite :0:.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* The empty set is equipotent to 0, which is a natural number.               *)
  apply WhenNat. apply Omega.HasZero.
Qed.

(* Every singleton is finite.                                                   *)
Proposition Single : forall (a:U), Finite :{a}:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a. exists :1:. split.
  - apply Omega.HasOne.
  - apply Equip.WhenSingle.
Qed.

(* A finite set remains finite after adjoining a single element.                *)
Proposition AddElem : forall (a b:U),
  Finite a -> Finite (a :\/: :{b}:).
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Apply AddElem which gives a :\/: :{b}: = a or a :\/: :{b}: ~ succ a.       *)
  intros a b [n [H1 [f H2]]].
  assert (a :\/: :{b}: = a \/ a :\/: :{b}: :~: succ a) as H3. {
    apply Equip.AddElem. }
  destruct H3 as [H3|H3].
  - (* b is already in a, so a :\/: :{b}: = a and we are done.                  *)
    rewrite H3. exists n. split. 1: assumption. exists f. assumption.
  - (* b not in a: a :\/: :{b}: ~ succ a, so ~ succ n which is in N.            *)
    exists (succ n). split.
    + apply Omega.HasSucc. assumption.
    + apply Equip.Tran with (succ a). 1: assumption.
      apply Equip.SuccCompat. exists f. assumption.
Qed.

(* Removing an element from a finite set leaves a finite set.                   *)
Proposition RemoveElem : forall (a b:U),
  Finite a -> Finite (a :\: :{b}:).
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* a :\: :{b}: is a subset of a, hence finite.                                *)
  intros a b H1. apply InclCompat with a. 2: assumption. apply Diff.IsIncl.
Qed.

(* The cardinal of a finite set is a natural number.                            *)
Proposition CardIsNat : forall (a:U),
  Finite a -> card a :< :N.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a [n [H1 H2]].
  (* A finite set is equipotent to some natural number n.                       *)
  assert (card a = card n) as H3. { apply Number.WhenEquip. assumption. }
  (* Natural numbers are their own cardinals.                                   *)
  assert (card n = n) as H4. { apply Number.WhenNat. assumption. }
  rewrite H3, H4. assumption.
Qed.

(* Assuming choice, a set whose cardinal is natural is finite.                  *)
Proposition WhenNatCard : forall (a:U), Choice ->
  card a :< :N -> Finite a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC H1. exists (card a). split. 1: assumption.
  (* Choice gives a bijection between a and its cardinal.                       *)
  apply WithChoice.IsEquip. assumption.
Qed.

(* A finite set with cardinal zero is empty.                                    *)
Proposition WhenZeroCard : forall (a:U),
  Finite a -> card a = :0: -> a = :0:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1 H2.
  (* Finiteness gives an ordinal equipotent to a, hence a is equipotent to its  *)
  (* cardinal.                                                                  *)
  assert (a :~: card a) as H3. {
    apply Number.IsEquip. destruct H1 as [n [H1 H3]].
    exists n. split. 2: assumption. apply Omega.HasOrdinals. assumption. }
  rewrite H2 in H3. apply Equip.WhenZero. assumption.
Qed.

(* Adding a new element to a finite set increments its cardinal.                *)
Proposition AddNewElem : forall (a b:U),
  Finite a                              ->
  ~ b :< a                              ->
  card (a :\/: :{b}:) = succ (card a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2.
  (* A finite set is equipotent to an ordinal, hence to its cardinal.           *)
  assert (WellOrderable a) as H3. {
    destruct H1 as [n [H1 H3]]. exists n. split. 2: assumption.
    apply Omega.HasOrdinals. assumption. }
  assert (a :~: card a) as H4. { apply Number.IsEquip. assumption. }
  (* Since b is new, adjoining b gives a set equipotent to succ(a).             *)
  assert (a :\/: :{b}: :~: succ a) as H5. {
    assert (a :\/: :{b}: = a \/ a :\/: :{b}: :~: succ a) as [H5|H5]. {
      apply Equip.AddElem. } 2: assumption.
    exfalso. apply H2. rewrite <- H5. apply Union2.Charac.
    right. apply Single.IsIn. }
  (* Transporting the bijection a ~ card(a) through successor gives the size.   *)
  assert (succ a :~: succ (card a)) as H6. {
    apply Equip.SuccCompat. assumption. }
  assert (a :\/: :{b}: :~: succ (card a)) as H7. {
    apply Equip.Tran with (succ a); assumption. }
  assert (card (a :\/: :{b}:) = card (succ (card a))) as H8. {
    apply Number.WhenEquip. assumption. }
  assert (card a :< :N) as H9. { apply CardIsNat. assumption. }
  assert (succ (card a) :< :N) as H10. { apply Omega.HasSucc. assumption. }
  assert (card (succ (card a)) = succ (card a)) as H11. {
    apply Number.WhenNat. assumption. }
  rewrite H8, H11. reflexivity.
Qed.

(* Removing an element from a set of cardinal succ(n) leaves cardinal n.        *)
Proposition RemoveElemCard : forall (n a b:U),
  n :< :N                   ->
  card a = succ n           ->
  b :< a                    ->
  card (a :\: :{b}:) = n.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros n a b H1 H2 H3.
  remember (a :\: :{b}:) as c eqn:H4.
  (* Since card(a) is a successor, a is equipotent to its cardinal.             *)
  assert (card a <> :0:) as H5. { rewrite H2. apply Succ.NotZero. }
  assert (a :~: card a) as H6. { apply Number.IsEquipNotZero. assumption. }
  (* Thus a is finite, being equipotent to the natural number succ(n).          *)
  assert (Finite a) as H7. {
    exists (succ n). split.
    - apply Omega.HasSucc. assumption.
    - rewrite <- H2. assumption. }
  assert (Finite c) as H8. { rewrite H4. apply RemoveElem. assumption. }
  (* The removed element is not in the remaining set.                           *)
  assert (~ b :< c) as H9. {
    rewrite H4. intros H9. apply Diff.Charac in H9.
    destruct H9 as [_ H9]. apply H9. apply Single.IsIn. }
  (* Adding the removed element back increments the remaining cardinal.         *)
  assert (card (c :\/: :{b}:) = succ (card c)) as H10. {
    apply AddNewElem; assumption. }
  assert (c :\/: :{b}: = a) as H11. {
    rewrite H4. apply Diff.RemoveAddElem. assumption. }
  rewrite H11, H2 in H10. apply Succ.Injective in H10.
  symmetry. assumption.
Qed.

(* The product of a singleton and a finite set is finite.                       *)
Proposition ProdSingleL : forall (a b:U),
  Finite a -> Finite (:{b}: :x: a).
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* {b} x a ~ a, so finiteness transfers from a to {b} x a.                    *)
  intros a b H1. apply EquipCompat with a. 2: assumption.
  apply Equip.Sym. apply Equip.ProdSingleL.
Qed.

(* The product of a finite set and a singleton is finite.                       *)
Proposition ProdSingleR : forall (a b:U),
  Finite a -> Finite (a :x: :{b}:).
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* a x {b} ~ a, so finiteness transfers from a to a x {b}.                    *)
  intros a b H1. apply EquipCompat with a. 2: assumption.
  apply Equip.Sym. apply Equip.ProdSingleR.
Qed.

(* The union of two finite sets is finite.                                      *)
Proposition Union : forall (a b:U),
  Finite a -> Finite b -> Finite (a :\/: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  remember (fun n => forall a b, card a = n ->
    Finite a -> Finite b -> Finite (a :\/: b)) as A eqn:H1.
  assert (forall n, n :< :N -> A n) as H2. {
    apply Omega.Induction; rewrite H1.
    - (* If card(a) is zero, then a is empty and the union is just b.           *)
      intros a b H2 H3 H4.
      assert (a = :0:) as H5. { apply WhenZeroCard; assumption. }
      rewrite H5, Union2.IdentityL. assumption.
    - (* If card(a) is succ(n), remove one element and use the induction step.  *)
      intros n H2 IH a b H4 H5 H6.
      assert (card a <> :0:) as H7. { rewrite H4. apply Succ.NotZero. }
      assert (a <> :0:) as H8. { apply Number.NotZero. assumption. }
      apply Empty.HasElem in H8. destruct H8 as [x H8].
      remember (a :\: :{x}:) as c eqn:H9.
      assert (card c = n) as H10. {
        rewrite H9. apply RemoveElemCard; assumption. }
      assert (Finite c) as H11. { rewrite H9. apply RemoveElem. assumption. }
      assert (Finite (c :\/: b)) as H12. { apply IH; assumption. }
      assert (a :\/: b = (c :\/: b) :\/: :{x}:) as H13. {
        assert (c :\/: :{x}: = a) as H14. {
          rewrite H9. apply Diff.RemoveAddElem. assumption. }
        (* Reordering the unions puts the removed element back at the end.      *)
        rewrite <- H14.
        rewrite (Union2.Assoc c :{x}: b).
        rewrite (Union2.Comm :{x}: b).
        rewrite <- (Union2.Assoc c b :{x}:).
        reflexivity. }
      rewrite H13. apply AddElem. assumption. }
  intros a b H3 H4.
  (* Apply the induction statement to card(a), which is natural by finiteness.  *)
  assert (A (card a)) as H5. { apply H2. apply CardIsNat. assumption. }
  rewrite H1 in H5. apply H5; try assumption. reflexivity.
Qed.

(* The product of two finite sets is finite.                                    *)
Proposition Prod : forall (a b:U),
  Finite a -> Finite b -> Finite (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  remember (fun n => forall a b, card a = n ->
    Finite a -> Finite b -> Finite (a :x: b)) as A eqn:H1.
  assert (forall n, n :< :N -> A n) as H2. {
    apply Omega.Induction; rewrite H1.
    - (* If card(a) is zero, then a is empty and so is its product with b.      *)
      intros a b H2 H3 H4.
      assert (a = :0:) as H5. { apply WhenZeroCard; assumption. }
      rewrite H5, Prod.ZeroL. apply Zero.
    - (* Remove one element from a and distribute product over the union.       *)
      intros n H2 IH a b H4 H5 H6.
      assert (card a <> :0:) as H7. { rewrite H4. apply Succ.NotZero. }
      assert (a <> :0:) as H8. { apply Number.NotZero. assumption. }
      apply Empty.HasElem in H8. destruct H8 as [x H8].
      remember (a :\: :{x}:) as c eqn:H9.
      assert (card c = n) as H10. {
        rewrite H9. apply RemoveElemCard; assumption. }
      assert (Finite c) as H11. { rewrite H9. apply RemoveElem. assumption. }
      assert (Finite (c :x: b)) as H12. { apply IH; assumption. }
      assert (Finite (:{x}: :x: b)) as H13. { apply ProdSingleL. assumption. }
      assert (a :x: b = c :x: b :\/: :{x}: :x: b) as H14. {
        assert (c :\/: :{x}: = a) as H15. {
          rewrite H9. apply Diff.RemoveAddElem. assumption. }
        (* Distributing the product separates the removed slice from the rest.  *)
        rewrite <- H15. apply Prod.DistribR. }
      rewrite H14. apply Union; assumption. }
  intros a b H3 H4.
  (* Apply the induction statement to card(a), which is natural by finiteness.  *)
  assert (A (card a)) as H5. { apply H2. apply CardIsNat. assumption. }
  rewrite H1 in H5. apply H5; try assumption. reflexivity.
Qed.

(* A surjective image of a finite set is finite.                                *)
Proposition OntoCompat : forall (f a b:U),
  Onto f a b -> Finite a -> Finite b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1 H2.
  assert (WellOrderable a) as H3. {
    destruct H2 as [n [H2 H3]]. exists n. split. 2: assumption.
    apply Omega.HasOrdinals. assumption. }
  (* A surjection from a well-orderable set makes the codomain well-orderable.  *)
  assert (WellOrderable b) as H4. {
    apply WellOrderable.OntoCompat with f a; assumption. }
  assert (card b :<=: card a) as H5. { apply Number.WhenOnto with f; assumption. }
  assert (card a :< :N) as H6. { apply CardIsNat. assumption. }
  (* The cardinal of b is bounded by a natural cardinal, hence is natural.      *)
  assert (card b :< :N) as H7. {
    apply Ordinal.InclElemTran with (card a); try assumption.
    - apply Number.IsOrdinal.
    - apply Number.IsOrdinal.
    - apply Omega.IsOrdinal. }
  exists (card b). split. 1: assumption. apply Number.IsEquip. assumption.
Qed.

(* The image of a finite set under a function is finite.                        *)
Proposition Image : forall (f a:U),
  FunctionOn f a -> Finite a -> Finite f:[a]:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a H1 H2. apply OntoCompat with f a. 2: assumption.
  split. 1: assumption. symmetry. apply FunctionOn.ImageOfDomain. assumption.
Qed.

(* The power set of a finite set is finite.                                     *)
Proposition Power : forall (a:U),
  Finite a -> Finite :P(a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  remember (fun n =>
    forall a, card a = n -> Finite a -> Finite :P(a)) as A eqn:H1.
  assert (forall n, n :< :N -> A n) as H2. {
    apply Omega.Induction; rewrite H1.
    - (* The only subset of the empty set is the empty set itself.              *)
      intros a H2 H3.
      assert (a = :0:) as H4. { apply WhenZeroCard; assumption. }
      rewrite H4, Power.WhenZero. apply Single.
    - (* A subset of a with one chosen element either omits it or contains it.  *)
      intros n H2 IH a H4 H5.
      assert (card a <> :0:) as H6. { rewrite H4. apply Succ.NotZero. }
      assert (a <> :0:) as H7. { apply Number.NotZero. assumption. }
      apply Empty.HasElem in H7. destruct H7 as [x H7].
      remember (a :\: :{x}:) as c eqn:H8.
      assert (card c = n) as H9. { rewrite H8. apply RemoveElemCard; assumption. }
      assert (Finite c) as H10. { rewrite H8. apply RemoveElem. assumption. }
      assert (Finite :P(c)) as H11. { apply IH; assumption. }
      (* Add the removed point to each subset of c.                             *)
      remember (from :P(c) (fun y => y :\/: :{x}:)) as f eqn:H12.
      assert (FunctionOn f :P(c)) as H13. { rewrite H12. apply From.IsFunctionOn. }
      (* The subsets of c that contain x form a finite image of P(c).           *)
      assert (Finite f:[:P(c)]:) as H14. { apply Image; assumption. }
      assert (Finite (:P(c) :\/: f:[:P(c)]:)) as H15. { apply Union; assumption. }
      assert (:P(a) :<=: :P(c) :\/: f:[:P(c)]:) as H16. {
        intros y H16. apply Power.Charac in H16.
        assert (x :< y \/ ~ x :< y) as [H17|H17]. { apply LawExcludedMiddle. }
        - apply Union2.Charac. right. apply Image.Charac.
          exists (y :\: :{x}:). split.
          + apply Power.Charac. intros z H18. rewrite H8. apply Diff.Charac.
            apply Diff.Charac in H18. destruct H18 as [H18 H19].
            split. 1: apply H16. assumption.
            intros H20. apply H19. apply Single.Charac in H20.
            apply Single.Charac. assumption.
          + rewrite H12. assert (y :\: :{x}: :< :P(c)) as H18. {
              apply Power.Charac. intros z H18. rewrite H8. apply Diff.Charac.
              apply Diff.Charac in H18. destruct H18 as [H18 H19].
              split. 1: apply H16. assumption.
              intros H20. apply H19. apply Single.Charac in H20.
              apply Single.Charac. assumption. }
            remember (y :\: :{x}:) as d eqn:H19.
            remember (d :\/: :{x}:) as e eqn:H20.
            assert (e = y) as H21. {
              rewrite H20, H19. apply Diff.RemoveAddElem. assumption. }
            assert (:(d,e): :< from :P(c) (fun y => y :\/: :{x}:)) as H22. {
              rewrite H20. apply (From.Satisfies (fun y => y :\/: :{x}:)
                :P(c) d). assumption. }
            rewrite H21 in H22.
            change (:(d,y): :< from :P(c) (fun y => y :\/: :{x}:)).
            assumption.
        - apply Union2.Charac. left. apply Power.Charac. intros z H18.
          rewrite H8. apply Diff.Charac. split. 1: apply H16. assumption.
          intros H19. apply Single.Charac in H19. subst. contradiction. }
      apply InclCompat with (:P(c) :\/: f:[:P(c)]:). 1: assumption.
      assumption. }
  intros a H3.
  assert (A (card a)) as H4. { apply H2. apply CardIsNat. assumption. }
  rewrite H1 in H4. apply H4; try assumption. reflexivity.
Qed.

(* The cardinal of the power set of a finite-cardinal set is finite.            *)
Proposition CardPower : forall (a:U),
  card a :< :N -> card :P(a) :< :N.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1.
  assert (WellOrderable a \/ ~ WellOrderable a) as [H2|H2]. {
    apply LawExcludedMiddle. }
  - (* If a is well-orderable, then a is actually finite.                       *)
    assert (Finite a) as H3. {
      exists (card a). split. 1: assumption. apply Number.IsEquip. assumption. }
    apply CardIsNat. apply Power. assumption.
  - (* Otherwise the power set cannot be well-orderable either.                 *)
    assert (~ WellOrderable :P(a)) as H3. {
      intros H3. apply H2. apply WellOrderable.PowerRev. assumption. }
    assert (card :P(a) = :0:) as H4. {
      apply Number.WhenNotWellOrderable. assumption. }
    rewrite H4. apply Omega.HasZero.
Qed.

(* An ordinal is finite if and only if it is a natural number.                  *)
Proposition WhenOrdinal : forall (a:U), Ordinal a ->
  Finite a <-> a :< :N.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1. split; intros H2.
  - (* A finite ordinal is equipotent to a natural number, hence equal to it.   *)
    destruct H2 as [n [H2 H3]].
    assert (a = n) as H4. { apply Equip.EqualOrdNat; assumption. }
    rewrite H4. assumption.
  - (* Conversely, every natural number is finite.                              *)
    apply WhenNat. assumption.
Qed.
