Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.Env.
Require Import ZF.Meta.Check.Shift.
Require Import ZF.Meta.Check.Subst.
Require Import ZF.Meta.Check.Ts.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.TypeOf.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Applying checked arguments to a variable preserves its sort.                 *)
Proposition VarT :
  forall (E:Env) (G D:Ctx) (ts:Terms) (n:nat) (ty:Ty),
    CheckTs E G ts (rev D)                  ->
    typeOf (D ++ G) n = Some ty             ->
    CheckT E G (applyT (Var n) ts) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G D ts n ty H1 H2.
  unfold applyT, substT. simpl.
  rewrite Nat.sub_0_r. rewrite ShiftZeroT.
  (* A variable from the substituted prefix is supplied by the checked terms.   *)
  destruct (Nat.lt_ge_cases n (length D)) as [H3|H3].
  - assert (typeOf D n = Some ty) as H4. {
      apply (TypeOf.AppSplitL D G); assumption.
    }
    rewrite TypeOf.NthError in H4.
    apply (ArgT E G ts D n); assumption.
    (* A later variable remains a variable in the surrounding context.          *)
  - assert (lengthT ts = length D) as H4. {
      rewrite <- length_rev. apply Length with E G. assumption.
    }
    assert (argT ts n = Var (n - lengthT ts)) as H5. {
      apply ArgTVar. rewrite H4. assumption.
    }
    rewrite H5. apply CheckVar.
    assert (typeOf G (n - length D) = Some ty) as H6. {
      apply (TypeOf.AppSplitR D G); assumption.
    }
    rewrite H4. assumption.
Qed.

(* Substitution by checked arguments preserves a variable across any cutoff.    *)
Proposition FromVarT :
  forall (E:Env) (G M D:Ctx) (ts:Terms) (n:nat) (ty:Ty),
    Check E                                                             ->
    CheckTs E D ts (rev M)                                              ->
    typeOf (G ++ M ++ D) n = Some ty                                    ->
    CheckT E (G ++ D) (Subst.fromT (length G) (argT ts) (Var n)) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G M D ts n ty H1 H2 H3.
  simpl.
  (* Variables in the left context are below the substitution cutoff.           *)
  destruct (Nat.lt_ge_cases n (length G)) as [H4|H4].
  - assert ((n <? length G) = true) as H5. { apply Nat.ltb_lt. assumption. }
    rewrite H5. apply CheckVar.
    assert (typeOf G n = Some ty) as H6. {
      apply (TypeOf.AppSplitL G (M ++ D)); assumption. }
    apply (TypeOf.AppL G D); assumption.
  - assert ((n <? length G) = false) as H5. { apply Nat.ltb_ge. assumption. }
    rewrite H5.
    (* Variables in the middle context are supplied by the checked arguments.   *)
    destruct (Nat.lt_ge_cases (n - length G) (length M)) as [H6|H6].
    + assert (typeOf (M ++ D) (n - length G) = Some ty) as H7. {
        apply (TypeOf.AppSplitR G (M ++ D)); assumption. }
      assert (CheckT E D (applyT (Var (n - length G)) ts) ty) as H8. {
        apply (VarT E D M); assumption. }
      assert (applyT (Var (n - length G)) ts = argT ts (n - length G)) as H9. {
        unfold applyT, substT. simpl. rewrite Nat.sub_0_r. rewrite ShiftZeroT.
        reflexivity. }
      assert (CheckT E (G ++ D)
        (Shift.fromT 0 (length G) (applyT (Var (n - length G)) ts)) ty) as H10. {
        apply (ZF.Meta.Check.Shift.FromT E) with (G := []) (M := G) (D := D).
        1: intros name tys t H11; apply (SigP E name); assumption.
        assumption. }
      simpl in H10. rewrite H9 in H10. assumption.
      (* Variables after the middle context remain variables in the tail.       *)
    + assert (typeOf (M ++ D) (n - length G) = Some ty) as H7. {
        apply (TypeOf.AppSplitR G (M ++ D)); assumption. }
      assert (typeOf D (n - length G - length M) = Some ty) as H8. {
        apply (TypeOf.AppSplitR M D); assumption. }
      assert (lengthT ts = length M) as H9. {
        rewrite <- length_rev. apply Length with E D. assumption. }
      assert (argT ts (n - length G) = Var (n - length G - lengthT ts)) as H10. {
        apply ArgTVar. rewrite H9. assumption. }
      rewrite H10. unfold shiftT. simpl.
      apply CheckVar.
      rewrite H9.
      assert (n - length G - length M + length G =
        length G + (n - length G - length M)) as H12. {
        rewrite Nat.add_comm. reflexivity. }
      rewrite H12. apply (TypeOf.AppR G D). assumption.
Qed.

(* Applying checked arguments to a checked term preserves its sort.             *)
Proposition ApplyT :
  forall (E:Env) (G D:Ctx) (t:Term) (ty:Ty) (ts:Terms),
    Check E                                                             ->
    CheckT E (D ++ G) t ty                                              ->
    CheckTs E G ts (rev D)                                              ->
    CheckT E G (applyT t ts) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G D t ty ts H1 H2 H3.
  unfold applyT, substT.
  apply (Subst.FromT E) with (G := []) (M := D) (D := G); assumption.
Qed.
