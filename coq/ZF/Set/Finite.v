Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.


Module SCC := ZF.Set.Cardinal.Core.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SPR := ZF.Set.Prod.


(* A set is finite if and only if it is equipotent to a natural number.         *)
Definition Finite (a:U) : Prop := exists n, n :< :N /\ a :~: n.

(* Finiteness is preserved under equipotence.                                   *)
Proposition EquivCompat : forall (a b:U),
  a :~: b -> Finite a -> Finite b.
Proof.
  (* Proof by Claude.                                                           *)
  (* a is finite so a ~ n for some n in N. Since a ~ b, b ~ a ~ n.              *)
  intros a b H1 [n [H2 H3]]. exists n. split. 1: assumption.
  apply SCE.Tran with a. 2: assumption.
  apply SCE.Sym. assumption.
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
    apply SCE.OrdinalSubset; assumption. }
  destruct H8 as [m [H8 [H9 H10]]].
  assert (m :< :N) as H11. { apply Core.InclElemTran with n; assumption. }
  assert (a :~: m) as H12. { apply SCE.Tran with f:[a]:; assumption. }
  exists m; split; assumption.
Qed.

Proposition WhenNat : forall (n:U), n :< :N -> Finite n.
Proof.
  intros n H1. exists n. split. 1: assumption. apply SCE.Refl.
Qed.

(* The empty set is finite.                                                     *)
Proposition Zero : Finite :0:.
Proof.
  (* Proof by Claude.                                                           *)
  (* The empty set is equipotent to 0, which is a natural number.               *)
  apply WhenNat. apply Omega.HasZero.
Qed.

(* A finite set remains finite after adjoining a single element.                *)
Proposition AddElem : forall (a b:U),
  Finite a -> Finite (a :\/: :{b}:).
Proof.
  (* Proof by Claude.                                                           *)
  (* Apply AddElem which gives a :\/: :{b}: = a or a :\/: :{b}: ~ succ a.       *)
  intros a b [n [H1 [f H2]]].
  assert (a :\/: :{b}: = a \/ a :\/: :{b}: :~: succ a) as H3. {
    apply SCE.AddElem. }
  destruct H3 as [H3|H3].
  - (* b is already in a, so a :\/: :{b}: = a and we are done.                  *)
    rewrite H3. exists n. split. 1: assumption. exists f. assumption.
  - (* b not in a: a :\/: :{b}: ~ succ a, so ~ succ n which is in N.            *)
    exists (succ n). split.
    + apply Omega.HasSucc. assumption.
    + apply SCE.Tran with (succ a). 1: assumption.
      apply SCE.SuccCompat. exists f. assumption.
Qed.

(* Removing an element from a finite set leaves a finite set.                   *)
Proposition RemoveElem : forall (a b:U),
  Finite a -> Finite (a :\: :{b}:).
Proof.
  (* Proof by Claude.                                                           *)
  (* a :\: :{b}: is a subset of a, hence finite.                                *)
  intros a b H1. apply InclCompat with a. 2: assumption. apply Diff.IsIncl.
Qed.

(* The cardinal of a finite set is a natural number.                            *)
Proposition CardIsNat : forall (a:U),
  Finite a -> card a :< :N.
Proof.
  (* Proof by Hermes.                                                           *)
  intros a [n [H1 H2]].
  (* A finite set is equipotent to some natural number n.                       *)
  assert (card a = card n) as H3. { apply SCC.WhenEquiv. assumption. }
  (* Natural numbers are their own cardinals.                                   *)
  assert (card n = n) as H4. { apply SCC.WhenNat. assumption. }
  rewrite H3, H4. assumption.
Qed.

(* Assuming choice, a set whose cardinal is natural is finite.                  *)
Proposition WhenNatCard : forall (a:U), Choice ->
  card a :< :N -> Finite a.
Proof.
  (* Proof by Hermes.                                                           *)
  intros a AC H1. exists (card a). split. 1: assumption.
  (* Choice gives a bijection between a and its cardinal.                       *)
  apply SCC.IsEquivChoice. assumption.
Qed.

(* A finite set with cardinal zero is empty.                                    *)
Proposition WhenZeroCard : forall (a:U),
  Finite a -> card a = :0: -> a = :0:.
Proof.
  (* Proof by Hermes.                                                           *)
  intros a H1 H2.
  (* Finiteness gives an ordinal equipotent to a, hence a is equipotent to its  *)
  (* cardinal.                                                                  *)
  assert (a :~: card a) as H3. {
    apply SCC.IsEquivGen. destruct H1 as [n [H1 H3]].
    exists n. split. 2: assumption. apply Omega.HasOrdinals. assumption. }
  rewrite H2 in H3. apply SCE.WhenZero. assumption.
Qed.

(* Adding a new element to a finite set increments its cardinal.                *)
Proposition AddNewElem : forall (a b:U),
  Finite a                              ->
  ~ b :< a                              ->
  card (a :\/: :{b}:) = succ (card a).
Proof.
  (* Proof by Hermes.                                                           *)
  intros a b H1 H2.
  (* A finite set is equipotent to an ordinal, hence to its cardinal.           *)
  assert (WithOrdinal a) as H3. {
    destruct H1 as [n [H1 H3]]. exists n. split. 2: assumption.
    apply Omega.HasOrdinals. assumption. }
  assert (a :~: card a) as H4. { apply SCC.IsEquivGen. assumption. }
  (* Since b is new, adjoining b gives a set equipotent to succ(a).             *)
  assert (a :\/: :{b}: :~: succ a) as H5. {
    assert (a :\/: :{b}: = a \/ a :\/: :{b}: :~: succ a) as [H5|H5]. {
      apply SCE.AddElem. } 2: assumption.
    exfalso. apply H2. rewrite <- H5. apply Union2.Charac.
    right. apply Single.IsIn. }
  (* Transporting the bijection a ~ card(a) through successor gives the size.   *)
  assert (succ a :~: succ (card a)) as H6. { apply SCE.SuccCompat. assumption. }
  assert (a :\/: :{b}: :~: succ (card a)) as H7. {
    apply SCE.Tran with (succ a); assumption. }
  assert (card (a :\/: :{b}:) = card (succ (card a))) as H8. {
    apply SCC.WhenEquiv. assumption. }
  assert (card a :< :N) as H9. { apply CardIsNat. assumption. }
  assert (succ (card a) :< :N) as H10. { apply Omega.HasSucc. assumption. }
  assert (card (succ (card a)) = succ (card a)) as H11. {
    apply SCC.WhenNat. assumption. }
  rewrite H8, H11. reflexivity.
Qed.

(* Removing an element from a set of cardinal succ(n) leaves cardinal n.        *)
Proposition RemoveElemCard : forall (n a b:U),
  n :< :N                   ->
  card a = succ n           ->
  b :< a                    ->
  card (a :\: :{b}:) = n.
Proof.
  (* Proof by Hermes.                                                           *)
  intros n a b H1 H2 H3.
  remember (a :\: :{b}:) as c eqn:H4.
  (* Since card(a) is a successor, a is equipotent to its cardinal.             *)
  assert (card a <> :0:) as H5. { rewrite H2. apply Succ.NotZero. }
  assert (a :~: card a) as H6. { apply SCC.IsEquivNotZero. assumption. }
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
  (* Proof by Claude.                                                           *)
  (* {b} x a ~ a, so finiteness transfers from a to {b} x a.                    *)
  intros a b H1. apply EquivCompat with a. 2: assumption.
  apply SCE.Sym. apply SCE.ProdSingleL.
Qed.

(* The product of a finite set and a singleton is finite.                       *)
Proposition ProdSingleR : forall (a b:U),
  Finite a -> Finite (a :x: :{b}:).
Proof.
  (* Proof by Claude.                                                           *)
  (* a x {b} ~ a, so finiteness transfers from a to a x {b}.                    *)
  intros a b H1. apply EquivCompat with a. 2: assumption.
  apply SCE.Sym. apply SCE.ProdSingleR.
Qed.

(* The union of two finite sets is finite.                                      *)
Proposition Union : forall (a b:U),
  Finite a -> Finite b -> Finite (a :\/: b).
Proof.
  (* Proof by Hermes.                                                           *)
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
      assert (a <> :0:) as H8. { apply SCC.NotZero. assumption. }
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
  (* Proof by Hermes.                                                           *)
  remember (fun n => forall a b, card a = n ->
    Finite a -> Finite b -> Finite (a :x: b)) as A eqn:H1.
  assert (forall n, n :< :N -> A n) as H2. {
    apply Omega.Induction; rewrite H1.
    - (* If card(a) is zero, then a is empty and so is its product with b.      *)
      intros a b H2 H3 H4.
      assert (a = :0:) as H5. { apply WhenZeroCard; assumption. }
      rewrite H5, SPR.ZeroL. apply Zero.
    - (* Remove one element from a and distribute product over the union.       *)
      intros n H2 IH a b H4 H5 H6.
      assert (card a <> :0:) as H7. { rewrite H4. apply Succ.NotZero. }
      assert (a <> :0:) as H8. { apply SCC.NotZero. assumption. }
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
        rewrite <- H15. apply SPR.DistribR. }
      rewrite H14. apply Union; assumption. }
  intros a b H3 H4.
  (* Apply the induction statement to card(a), which is natural by finiteness.  *)
  assert (A (card a)) as H5. { apply H2. apply CardIsNat. assumption. }
  rewrite H1 in H5. apply H5; try assumption. reflexivity.
Qed.
