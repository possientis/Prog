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
Proposition Above :
  (forall (E:Env) (G:Ctx) (t:Term) (ty:Ty) (i:nat) (r:nat -> Term),
    Check E                                                                 ->
    CheckT E G t ty                                                         ->
    length G <= i                                                           ->
    fromT i r t = t)                                                        /\
  (forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty) (i:nat) (r:nat -> Term),
    Check E                                                                 ->
    CheckTs E G ts tys                                                      ->
    length G <= i                                                           ->
    fromTs i r ts = ts)                                                     /\
  (forall (E:Env) (G:Ctx) (p:Proof) (t:Term) (i:nat) (r:nat -> Term),
    Check E                                                                 ->
    CheckP E G p t                                                          ->
    length G <= i                                                           ->
    fromP i r p = p).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (
    (forall (E:Env) (G:Ctx) (t:Term) (ty:Ty),
      CheckT E G t ty                                                       ->
      forall (i:nat) (r:nat -> Term),
      Check E -> length G <= i -> fromT i r t = t)                          /\
    (forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty),
      CheckTs E G ts tys                                                    ->
      forall (i:nat) (r:nat -> Term),
      Check E -> length G <= i -> fromTs i r ts = ts)                       /\
    (forall (E:Env) (G:Ctx) (p:Proof) (t:Term),
      CheckP E G p t                                                        ->
      forall (i:nat) (r:nat -> Term),
      Check E -> length G <= i -> fromP i r p = p)) as H. {
    apply Induction.
    - intros E G i r H1 H2. reflexivity.
    - intros E G i r H1 H2. reflexivity.
    - intros E G n ty H1 i r H2 H3. simpl.
      (* A checked variable is below the substitution cutoff.                   *)
      assert (n < length G) as H4. { apply (TypeOf.LtLength G n ty). assumption. }
      assert (n < i) as H5. {
        apply Nat.lt_le_trans with (m := length G); assumption. }
      assert ((n <? i) = true) as H6. { apply Nat.ltb_lt. assumption. }
      rewrite H6. reflexivity.
    - intros E G ty i r H1 H2. reflexivity.
    - intros E G name args tys ty H1 H2 H3 i r H4 H5. simpl.
      rewrite H3; try assumption. reflexivity.
    - intros E G x y H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G x y H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G x y H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G x y H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G x y H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G x y H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G x y H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G p q H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G p q H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G p q H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G p q H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G p H1 H2 i r H3 H4. simpl. rewrite H2; try assumption. reflexivity.
    - intros E G p H1 H2 i r H3 H4. simpl.
      rewrite H2. reflexivity. assumption. apply le_n_S. assumption.
    - intros E G p H1 H2 i r H3 H4. simpl.
      rewrite H2. reflexivity. assumption. apply le_n_S. assumption.
    - intros E G p H1 H2 i r H3 H4. simpl.
      rewrite H2. reflexivity. assumption. apply le_n_S. assumption.
    - intros E G A x H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G A p q H1 H2 H3 H4 H5 H6 i r H7 H8. simpl.
      rewrite H2, H4, H6; try assumption. reflexivity.
    - intros E G i r H1 H2. reflexivity.
    - intros E G t ts ty tys H1 H2 H3 H4 i r H5 H6. simpl.
      rewrite H2, H4; try assumption. reflexivity.
    - intros E G t H1 H2 i r H3 H4. simpl. rewrite H2; try assumption. reflexivity.
    - intros E G t H1 H2 i r H3 H4. simpl. rewrite H2; try assumption. reflexivity.
    - intros E G name args tys t H1 H2 H3 i r H4 H5. simpl.
      rewrite H3; try assumption. reflexivity. }
  destruct H as [H1 [H2 H3]]. split.
  - intros E G t ty i r H4 H5 H6.
    apply H1 with (E := E) (G := G) (ty := ty); assumption.
  - split.
    + intros E G ts tys i r H4 H5 H6.
      apply H2 with (E := E) (G := G) (tys := tys); assumption.
    + intros E G p t i r H4 H5 H6.
      apply H3 with (E := E) (G := G) (t := t); assumption.
Qed.

(* Substitution above a checked term leaves it unchanged.                       *)
Proposition AboveT :
  forall (E:Env) (G:Ctx) (t:Term) (ty:Ty) (i:nat) (r:nat -> Term),
    Check E                                                                 ->
    CheckT E G t ty                                                         ->
    length G <= i                                                           ->
    fromT i r t = t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.

(* Substitution above checked term arguments leaves them unchanged.             *)
Proposition AboveTs :
  forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty) (i:nat) (r:nat -> Term),
    Check E                                                                 ->
    CheckTs E G ts tys                                                      ->
    length G <= i                                                           ->
    fromTs i r ts = ts.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.

(* Substitution above a checked proof leaves it unchanged.                      *)
Proposition AboveP :
  forall (E:Env) (G:Ctx) (p:Proof) (t:Term) (i:nat) (r:nat -> Term),
    Check E                                                                 ->
    CheckP E G p t                                                          ->
    length G <= i                                                           ->
    fromP i r p = p.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.


(* Substitution by checked arguments preserves checked objects.                 *)
Proposition From :
  (forall (E:Env) (G M D:Ctx) (t:Term) (ty:Ty) (ts:Terms),
    Check E                                                                 ->
    CheckT E (G ++ M ++ D) t ty                                             ->
    CheckTs E D ts (rev M)                                                  ->
    CheckT E (G ++ D) (fromT (length G) (argT ts) t) ty)                    /\
  (forall (E:Env) (G M D:Ctx) (us:Terms) (tys:list Ty) (ts:Terms),
    Check E                                                                 ->
    CheckTs E (G ++ M ++ D) us tys                                          ->
    CheckTs E D ts (rev M)                                                  ->
    CheckTs E (G ++ D) (fromTs (length G) (argT ts) us) tys)                /\
  (forall (E:Env) (G M D:Ctx) (p:Proof) (t:Term) (ts:Terms),
    Check E                                                                 ->
    CheckP E (G ++ M ++ D) p t                                              ->
    CheckTs E D ts (rev M)                                                  ->
    CheckP E (G ++ D) (fromP (length G) (argT ts) p)
      (fromT (length G) (argT ts) t)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (
    (forall (E:Env) (C:Ctx) (t:Term) (ty:Ty), CheckT E C t ty               ->
      Check E                                                               ->
      forall (G M D:Ctx) (ts:Terms), C = G ++ M ++ D                        ->
      CheckTs E D ts (rev M)                                                ->
      CheckT E (G ++ D) (fromT (length G) (argT ts) t) ty)                  /\
    (forall (E:Env) (C:Ctx) (us:Terms) (tys:list Ty), CheckTs E C us tys    ->
      Check E                                                               ->
      forall (G M D:Ctx) (ts:Terms), C = G ++ M ++ D                        ->
      CheckTs E D ts (rev M)                                                ->
      CheckTs E (G ++ D) (fromTs (length G) (argT ts) us) tys)              /\
    (forall (E:Env) (C:Ctx) (p:Proof) (t:Term), CheckP E C p t              ->
      Check E                                                               ->
      forall (G M D:Ctx) (ts:Terms), C = G ++ M ++ D                        ->
      CheckTs E D ts (rev M)                                                ->
      CheckP E (G ++ D) (fromP (length G) (argT ts) p)
        (fromT (length G) (argT ts) t))) as H2. {
    apply Induction.
    - intros E C H1 G M D ts H2 H3. subst. apply CheckBot.
    - intros E C H1 G M D ts H2 H3. subst. apply CheckTop.
    - intros E C n ty H1 H2 G M D ts H3 H4. subst. simpl.
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
          assert (
            applyT (Var (n - length G)) ts = argT ts (n - length G)) as H10. {
            unfold applyT, substT. simpl. rewrite Nat.sub_0_r. rewrite ShiftZeroT.
            reflexivity. }
          assert (CheckT E (G ++ D)
            (Shift.fromT 0
              (length G) (applyT (Var (n - length G)) ts)) ty) as H11. {
            apply (ZF.Meta.Check.Shift.FromT E) with (G := []) (M := G) (D := D);
            assumption. }
          simpl in H11. rewrite H10 in H11. assumption.
        * assert (typeOf (M ++ D) (n - length G) = Some ty) as H8. {
            apply (TypeOf.AppSplitR G (M ++ D)); assumption. }
          assert (typeOf D (n - length G - length M) = Some ty) as H9. {
            apply (TypeOf.AppSplitR M D); assumption. }
          assert (lengthT ts = length M) as H10. {
            rewrite <- length_rev. apply Length with E D. assumption. }
          assert (
            argT ts (n - length G) = Var (n - length G - lengthT ts)) as H11. {
            apply ArgTVar. rewrite H10. assumption. }
          rewrite H11. unfold shiftT. simpl.
          apply CheckVar. rewrite H10.
          assert (
            n - length G - length M + length G =
            length G + (n - length G - length M)) as H12. {
            rewrite Nat.add_comm. reflexivity. }
          rewrite H12. apply (TypeOf.AppR G D). assumption.
    - intros E C ty H1 G M D ts H2 H3. subst. apply CheckHoleT.
    - intros E C name args tys ty H1 H2 H3 H4 G M D ts H5 H6. subst.
      apply CheckIdentT with tys. 1: assumption.
      apply H3 with M; try assumption. reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckElem.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckLeq.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckGeq.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckLt.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckGt.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckEqual.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckNotEq.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C p q H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckImp.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C p q H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckIff.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C p q H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckAnd.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C p q H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckOr.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C p H2 H3 H4 G M D ts H5 H6. subst. apply CheckNot.
      apply H3 with M; try assumption. reflexivity.
    - intros E C p H2 H3 H4 G M D ts H5 H6. subst. apply CheckAll.
      apply H3 with (G := TySet :: G) (M := M); try assumption. reflexivity.
    - intros E C p H2 H3 H4 G M D ts H5 H6. subst. apply CheckEx.
      apply H3 with (G := TySet :: G) (M := M); try assumption. reflexivity.
    - intros E C p H2 H3 H4 G M D ts H5 H6. subst. apply CheckLam.
      apply H3 with (G := TySet :: G) (M := M); try assumption. reflexivity.
    - intros E C A x H2 H3 H4 H5 H6 G M D ts H7 H8. subst. apply CheckApp.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C A p q H2 H3 H4 H5 H6 H7 H8 G M D ts H9 H10.
      subst. apply CheckDef.
      + apply H3 with M; try assumption. reflexivity.
      + assert (CheckP E (G ++ D) (fromP (length G) (argT ts) p)
          (fromT (length G) (argT ts) (Exists A))) as H9. {
          apply H5 with (G := G) (M := M) (D := D) (ts := ts); try assumption.
          reflexivity. }
        rewrite Exists.SubstT in H9. assumption.
      + assert (CheckP E (G ++ D) (fromP (length G) (argT ts) q)
          (fromT (length G) (argT ts) (Unique A))) as H9. {
          apply H7 with (G := G) (M := M) (D := D) (ts := ts); try assumption.
          reflexivity. }
        rewrite Unique.SubstT in H9. assumption.
    - intros E C H1 G M D ts H2 H3. subst. apply CheckTsNil.
    - intros E C t us ty tys H2 H3 H4 H5 H6 G M D ts H7 H8.
      subst. apply CheckTsCons.
      + apply H3 with M; try assumption. reflexivity.
      + apply H5 with M; try assumption. reflexivity.
    - intros E C t H2 H3 H4 G M D ts H5 H6. subst. apply CheckHoleP.
      apply H3 with M; try assumption. reflexivity.
    - intros E C t H2 H3 H4 G M D ts H5 H6. subst. apply CheckAxiomP.
      apply H3 with M; try assumption. reflexivity.
    - intros E C name args tys t H2 H3 H4 H5 G M D ts H6 H7. subst.
      rewrite Apply.FromT.
      assert (fromT (length G + lengthT args) (argT ts) t = t) as H6. {
        apply (AboveT E (rev tys) t TyProp (length G + lengthT args) (argT ts)).
        - assumption.
        - apply (SigP E name); assumption.
        - rewrite length_rev.
          assert (lengthT args = length tys) as H6. {
            apply (Length E (G ++ M ++ D)); assumption. }
          rewrite <- H6. rewrite Nat.add_comm. apply Nat.le_add_r. }
      rewrite H6. apply CheckIdentP with (tys := tys). 1: assumption.
      apply H4 with (G := G) (M := M) (D := D) (ts := ts);
      try assumption. reflexivity. }
  split.
  - intros E G M D t ty ts H3 H4 H5.
    apply H2 with (C := G ++ M ++ D) (G := G) (M := M);
    try assumption. reflexivity.
  - split.
    + intros E G M D us tys ts H3 H4 H5.
      apply H2 with (C := G ++ M ++ D) (G := G) (M := M);
      try assumption. reflexivity.
    + intros E G M D p t ts H3 H4 H5.
      apply H2 with (C := G ++ M ++ D) (G := G) (M := M);
      try assumption. reflexivity.
Qed.

(* Substitution by checked arguments preserves checked terms.                   *)
Proposition FromT :
  forall (E:Env) (G M D:Ctx) (t:Term) (ty:Ty) (ts:Terms),
    Check E                                                               ->
    CheckT E (G ++ M ++ D) t ty                                           ->
    CheckTs E D ts (rev M)                                                ->
    CheckT E (G ++ D) (fromT (length G) (argT ts) t) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

(* Substitution by checked arguments preserves checked term arguments.          *)
Proposition FromTs :
  forall (E:Env) (G M D:Ctx) (us:Terms) (tys:list Ty) (ts:Terms),
    Check E                                                               ->
    CheckTs E (G ++ M ++ D) us tys                                        ->
    CheckTs E D ts (rev M)                                                ->
    CheckTs E (G ++ D) (fromTs (length G) (argT ts) us) tys.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

(* Substitution by checked arguments preserves checked proofs.                  *)
Proposition FromP :
  forall (E:Env) (G M D:Ctx) (p:Proof) (t:Term) (ts:Terms),
    Check E                                                               ->
    CheckP E (G ++ M ++ D) p t                                            ->
    CheckTs E D ts (rev M)                                                ->
    CheckP E (G ++ D) (fromP (length G) (argT ts) p)
      (fromT (length G) (argT ts) t).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

