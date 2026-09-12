Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.Env.
Require Import ZF.Meta.Check.Induction.
Require Import ZF.Meta.Check.Shift.
Require Import ZF.Meta.Check.Ts.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Exists.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.TypeOf.
Require Import ZF.Meta.Ty.
Require Import ZF.Meta.Unique.

Import ListNotations.

(* Substitution above a checked object leaves it unchanged.                     *)
Proposition Above : forall (E:Env),
  (forall (G:Ctx) (t:Term) (ty:Ty),
    CheckT E G t ty -> Check E -> forall (i:nat) (r:nat -> Term),
    length G <= i -> fromT i r t = t)                                      /\
  (forall (G:Ctx) (ts:Terms) (tys:list Ty),
    CheckTs E G ts tys -> Check E -> forall (i:nat) (r:nat -> Term),
    length G <= i -> fromTs i r ts = ts)                                   /\
  (forall (G:Ctx) (p:Proof) (t:Term),
    CheckP E G p t -> Check E -> forall (i:nat) (r:nat -> Term),
    length G <= i -> fromP i r p = p).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E.
  apply Induction.
  - intros G H1 i r H2. reflexivity.
  - intros G H1 i r H2. reflexivity.
  - intros G n ty H1 H2 i r H3. simpl.
    (* A checked variable is below the substitution cutoff.                     *)
    assert (n < length G) as H4. { apply (TypeOf.LtLength G n ty). assumption. }
    assert (n < i) as H5. { apply Nat.lt_le_trans with (m := length G); assumption. }
    assert ((n <? i) = true) as H6. { apply Nat.ltb_lt. assumption. }
    rewrite H6. reflexivity.
  - intros G ty H1 i r H2. reflexivity.
  - intros G name args tys ty H1 H2 H3 H4 i r H5. simpl.
    rewrite H3; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G p q H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G p q H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G p q H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G p q H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G p H1 H2 H3 i r H4. simpl. rewrite H2; try assumption. reflexivity.
  - intros G p H1 H2 H3 i r H4. simpl.
    rewrite H2. reflexivity. assumption. apply le_n_S. assumption.
  - intros G p H1 H2 H3 i r H4. simpl.
    rewrite H2. reflexivity. assumption. apply le_n_S. assumption.
  - intros G p H1 H2 H3 i r H4. simpl.
    rewrite H2. reflexivity. assumption. apply le_n_S. assumption.
  - intros G A x H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G A p q H1 H2 H3 H4 H5 H6 H7 i r H8. simpl.
    rewrite H2, H4, H6; try assumption. reflexivity.
  - intros G H1 i r H2. reflexivity.
  - intros G t ts ty tys H1 H2 H3 H4 H5 i r H6. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G t H1 H2 H3 i r H4. simpl. rewrite H2; try assumption. reflexivity.
  - intros G t H1 H2 H3 i r H4. simpl. rewrite H2; try assumption. reflexivity.
  - intros G name args tys t H1 H2 H3 H4 i r H5. simpl.
    rewrite H3; try assumption. reflexivity.
Qed.

(* Substitution above a checked term leaves it unchanged.                       *)
Proposition AboveT : forall (E:Env) (G:Ctx) (t:Term) (ty:Ty),
  CheckT E G t ty -> Check E -> forall (i:nat) (r:nat -> Term),
  length G <= i -> fromT i r t = t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.

(* Substitution above checked term arguments leaves them unchanged.             *)
Proposition AboveTs : forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty),
  CheckTs E G ts tys -> Check E -> forall (i:nat) (r:nat -> Term),
  length G <= i -> fromTs i r ts = ts.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.

(* Substitution above a checked proof leaves it unchanged.                      *)
Proposition AboveP : forall (E:Env) (G:Ctx) (p:Proof) (t:Term),
  CheckP E G p t -> Check E -> forall (i:nat) (r:nat -> Term),
  length G <= i -> fromP i r p = p.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.


(* Substitution by checked arguments preserves checked objects.                 *)
Proposition From : forall (E:Env), Check E ->
  (forall (G M D:Ctx) (t:Term) (ty:Ty) (ts:Terms),
    CheckT E (G ++ M ++ D) t ty                                 ->
    CheckTs E D ts (rev M)                                      ->
    CheckT E (G ++ D) (fromT (length G) (argT ts) t) ty)              /\
  (forall (G M D:Ctx) (us:Terms) (tys:list Ty) (ts:Terms),
    CheckTs E (G ++ M ++ D) us tys                              ->
    CheckTs E D ts (rev M)                                      ->
    CheckTs E (G ++ D) (fromTs (length G) (argT ts) us) tys)          /\
  (forall (G M D:Ctx) (p:Proof) (t:Term) (ts:Terms),
    CheckP E (G ++ M ++ D) p t                                  ->
    CheckTs E D ts (rev M)                                      ->
    CheckP E (G ++ D) (fromP (length G) (argT ts) p)
      (fromT (length G) (argT ts) t)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E H1.
  assert (
    (forall (C:Ctx) (t:Term) (ty:Ty), CheckT E C t ty ->
      forall (G M D:Ctx) (ts:Terms), C = G ++ M ++ D ->
      CheckTs E D ts (rev M) ->
      CheckT E (G ++ D) (fromT (length G) (argT ts) t) ty)               /\
    (forall (C:Ctx) (us:Terms) (tys:list Ty), CheckTs E C us tys ->
      forall (G M D:Ctx) (ts:Terms), C = G ++ M ++ D ->
      CheckTs E D ts (rev M) ->
      CheckTs E (G ++ D) (fromTs (length G) (argT ts) us) tys)           /\
    (forall (C:Ctx) p (t:Term), CheckP E C p t ->
      forall (G M D:Ctx) (ts:Terms), C = G ++ M ++ D ->
      CheckTs E D ts (rev M) ->
      CheckP E (G ++ D) (fromP (length G) (argT ts) p)
        (fromT (length G) (argT ts) t))) as H2. {
    apply Induction.
    - intros C G M D ts H2 H3. subst. apply CheckBot.
    - intros C G M D ts H2 H3. subst. apply CheckTop.
    - intros C n ty H2 G M D ts H3 H4. subst. simpl.
      (* Variables before, inside, and after the middle context are handled.    *)
      destruct (Nat.lt_ge_cases n (length G)) as [H5|H5].
      + assert ((n <? length G) = true) as H6. { apply Nat.ltb_lt. assumption. }
        rewrite H6. apply CheckVar.
        assert (typeOf G n = Some ty) as H7. {
          apply (TypeOf.AppSplitL G (M ++ D)); assumption. }
        apply (TypeOf.AppL G D). assumption.
      + assert ((n <? length G) = false) as H6. { apply Nat.ltb_ge. assumption. }
        rewrite H6.
        destruct (Nat.lt_ge_cases (n - length G) (length M)) as [H7|H7].
        * assert (typeOf (M ++ D) (n - length G) = Some ty) as H8. {
            apply (TypeOf.AppSplitR G (M ++ D)); assumption. }
          assert (CheckT E D (applyT (Var (n - length G)) ts) ty) as H9. {
            unfold applyT, substT. simpl. rewrite Nat.sub_0_r. rewrite ShiftZeroT.
            assert (typeOf M (n - length G) = Some ty) as H9. {
              apply (TypeOf.AppSplitL M D); assumption. }
            rewrite TypeOf.NthError in H9. apply (ArgT E D ts M); assumption. }
          assert (applyT (Var (n - length G)) ts = argT ts (n - length G)) as H10. {
            unfold applyT, substT. simpl. rewrite Nat.sub_0_r. rewrite ShiftZeroT.
            reflexivity. }
          assert (CheckT E (G ++ D)
            (Shift.fromT 0 (length G) (applyT (Var (n - length G)) ts)) ty) as H11. {
            apply (ZF.Meta.Check.Shift.FromT E) with (G := []) (M := G) (D := D).
            1: intros name tys u H12; apply (SigP E name); assumption.
            assumption. }
          simpl in H11. rewrite H10 in H11. assumption.
        * assert (typeOf (M ++ D) (n - length G) = Some ty) as H8. {
            apply (TypeOf.AppSplitR G (M ++ D)); assumption. }
          assert (typeOf D (n - length G - length M) = Some ty) as H9. {
            apply (TypeOf.AppSplitR M D); assumption. }
          assert (lengthT ts = length M) as H10. {
            rewrite <- length_rev. apply Length with E D. assumption. }
          assert (argT ts (n - length G) = Var (n - length G - lengthT ts)) as H11. {
            apply ArgTVar. rewrite H10. assumption. }
          rewrite H11. unfold shiftT. simpl.
          apply CheckVar. rewrite H10.
          assert (n - length G - length M + length G =
            length G + (n - length G - length M)) as H12. {
            rewrite Nat.add_comm. reflexivity. }
          rewrite H12. apply (TypeOf.AppR G D). assumption.
    - intros C ty G M D ts H2 H3. subst. apply CheckHoleT.
    - intros C name args tys ty H2 H3 H4 G M D ts H5 H6. subst. simpl.
      apply CheckIdentT with (tys := tys).
      1: assumption. apply (H4 G M D ts); try assumption. reflexivity.
    - intros C x y H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckElem.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C x y H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckLeq.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C x y H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckGeq.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C x y H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckLt.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C x y H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckGt.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C x y H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckEqual.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C x y H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckNotEq.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C p q H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckImp.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C p q H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckIff.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C p q H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckAnd.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C p q H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckOr.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C p H2 H3 G M D ts H4 H5. subst. simpl.
      apply CheckNot. apply (H3 G M D ts); try assumption. reflexivity.
    - intros C p H2 H3 G M D ts H4 H5. subst. simpl.
      apply CheckAll. apply (H3 (TySet :: G) M D); try assumption. reflexivity.
    - intros C p H2 H3 G M D ts H4 H5. subst. simpl.
      apply CheckEx. apply (H3 (TySet :: G) M D); try assumption. reflexivity.
    - intros C p H2 H3 G M D ts H4 H5. subst. simpl.
      apply CheckLam. apply (H3 (TySet :: G) M D); try assumption. reflexivity.
    - intros C A x H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckApp.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C A p q H2 H3 H4 H5 H6 H7 G M D ts H8 H9. subst. simpl.
      apply CheckDef.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + assert (CheckP E (G ++ D) (fromP (length G) (argT ts) p)
          (fromT (length G) (argT ts) (Exists A))) as H8. {
          apply (H5 G M D ts); try assumption. reflexivity. }
        assert (fromT (length G) (argT ts) (Exists A) =
          Exists (fromT (length G) (argT ts) A)) as H10. {
          unfold Exists, shiftT. simpl.
          assert (S (length G) = 0 + 1 + length G) as H10. { reflexivity. }
          rewrite H10. rewrite (proj1 ShiftFrom). simpl.
          reflexivity. }
        rewrite H10 in H8. assumption.
      + assert (CheckP E (G ++ D) (fromP (length G) (argT ts) q)
          (fromT (length G) (argT ts) (Unique A))) as H8. {
          apply (H7 G M D ts); try assumption. reflexivity. }
        assert (fromT (length G) (argT ts) (Unique A) =
          Unique (fromT (length G) (argT ts) A)) as H10. {
          unfold Unique, shiftT. simpl.
          assert (S (S (length G)) = 0 + 2 + length G) as H10. { reflexivity. }
          rewrite H10. rewrite (proj1 ShiftFrom). simpl.
          reflexivity. }
        rewrite H10 in H8. assumption.
    - intros C G M D ts H2 H3. subst. simpl. apply CheckTsNil.
    - intros C t us ty tys H2 H3 H4 H5 G M D ts H6 H7. subst. simpl.
      apply CheckTsCons.
      + apply (H3 G M D ts); try assumption. reflexivity.
      + apply (H5 G M D ts); try assumption. reflexivity.
    - intros C t H2 H3 G M D ts H4 H5. subst. simpl.
      apply CheckHoleP. apply (H3 G M D ts); try assumption. reflexivity.
    - intros C t H2 H3 G M D ts H4 H5. subst. simpl.
      apply CheckAxiomP. apply (H3 G M D ts); try assumption. reflexivity.
    - intros C name args tys t H2 H3 H4 G M D ts H5 H6. subst. simpl.
      rewrite Apply.FromT.
      assert (fromT (length G + lengthT args) (argT ts) t = t) as H5. {
        apply (AboveT E (rev tys) t TyProp).
        - apply (SigP E name); assumption.
        - assumption.
        - rewrite length_rev.
          assert (lengthT args = length tys) as H5. {
            apply (Length E (G ++ M ++ D)); assumption. }
          rewrite <- H5. rewrite Nat.add_comm. apply Nat.le_add_r. }
      rewrite H5.
      apply CheckIdentP with (tys := tys).
      1: assumption. apply (H4 G M D ts); try assumption. reflexivity. }
  destruct H2 as [H2 [H3 H4]].
  split.
  - intros G M D t ty ts H5 H6.
    apply (H2 (G ++ M ++ D) t ty H5 G M D ts); try assumption. reflexivity.
  - split.
    + intros G M D us tys ts H5 H6.
      apply (H3 (G ++ M ++ D) us tys H5 G M D ts); try assumption.
      reflexivity.
    + intros G M D p t ts H5 H6.
      apply (H4 (G ++ M ++ D) p t H5 G M D ts); try assumption.
      reflexivity.
Qed.

(* Substitution by checked arguments preserves checked terms.                   *)
Proposition FromT : forall (E:Env), Check E ->
  forall (G M D:Ctx) (t:Term) (ty:Ty) (ts:Terms),
    CheckT E (G ++ M ++ D) t ty                                 ->
    CheckTs E D ts (rev M)                                      ->
    CheckT E (G ++ D) (fromT (length G) (argT ts) t) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

(* Substitution by checked arguments preserves checked term arguments.          *)
Proposition FromTs : forall (E:Env), Check E ->
  forall (G M D:Ctx) (us:Terms) (tys:list Ty) (ts:Terms),
    CheckTs E (G ++ M ++ D) us tys                              ->
    CheckTs E D ts (rev M)                                      ->
    CheckTs E (G ++ D) (fromTs (length G) (argT ts) us) tys.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

(* Substitution by checked arguments preserves checked proofs.                  *)
Proposition FromP : forall (E:Env), Check E ->
  forall (G M D:Ctx) (p:Proof) (t:Term) (ts:Terms),
    CheckP E (G ++ M ++ D) p t                                  ->
    CheckTs E D ts (rev M)                                      ->
    CheckP E (G ++ D) (fromP (length G) (argT ts) p)
      (fromT (length G) (argT ts) t).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.
