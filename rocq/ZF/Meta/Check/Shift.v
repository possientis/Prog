Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.Induction.
Require Import ZF.Meta.Check.Ts.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Exists.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.TypeOf.
Require Import ZF.Meta.Ty.
Require Import ZF.Meta.Unique.

Import ListNotations.

(* Weakening preserves a checked variable across an inserted context.           *)
Proposition VarT : forall (E:Env) (G M D:Ctx) (n:nat) (ty:Ty),
  typeOf (G ++ D) n = Some ty ->
  CheckT E (G ++ M ++ D) (Shift.fromT (length G) (length M) (Var n)) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G M D n ty H1.
  simpl.
  (* A variable in the left context is not shifted by inserting the middle.     *)
  destruct (Nat.lt_ge_cases n (length G)) as [H2|H2].
  - assert ((n <? length G) = true) as H3. { apply Nat.ltb_lt. assumption. }
    rewrite H3. apply CheckVar.
    apply (TypeOf.ThreeL G M D); assumption.
    (* A variable in the right context is shifted past the inserted middle.     *)
  - assert ((n <? length G) = false) as H3. { apply Nat.ltb_ge. assumption. }
    rewrite H3. apply CheckVar.
    apply (TypeOf.ThreeR G M D); assumption.
Qed.

(* Lifting above a checked object leaves it unchanged.                          *)
Proposition Above : forall (E:Env),
  (forall (G:Ctx) (t:Term) (ty:Ty) (i j:nat),
    CheckT E G t ty -> length G <= i ->
    Shift.fromT i j t = t)                                               /\
  (forall (G:Ctx) (ts:Terms) (tys:list Ty) (i j:nat),
    CheckTs E G ts tys -> length G <= i ->
    Shift.fromTs i j ts = ts)                                            /\
  (forall (G:Ctx) (p:Proof) (t:Term) (i j:nat),
    CheckP E G p t -> length G <= i ->
    Shift.fromP i j p = p).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E.
  assert (
    (forall (G:Ctx) (t:Term) (ty:Ty),
      CheckT E G t ty -> forall (i j:nat), length G <= i ->
      Shift.fromT i j t = t)                                             /\
    (forall (G:Ctx) (ts:Terms) (tys:list Ty),
      CheckTs E G ts tys -> forall (i j:nat), length G <= i ->
      Shift.fromTs i j ts = ts)                                          /\
    (forall (G:Ctx) p (t:Term),
      CheckP E G p t -> forall (i j:nat), length G <= i ->
      Shift.fromP i j p = p)) as H1. {
    apply Induction.
  - intros G i j H1. reflexivity.
  - intros G i j H1. reflexivity.
  - intros G n ty H1 i j H2. simpl.
    (* A checked variable is below the length of its context.                   *)
    assert (n < length G) as H3. { apply (TypeOf.LtLength G n ty). assumption. }
    assert (n < i) as H4. { apply Nat.lt_le_trans with (m := length G); assumption. }
    assert ((n <? i) = true) as H5. { apply Nat.ltb_lt. assumption. }
    rewrite H5. reflexivity.
  - intros G ty i j H1. reflexivity.
  - intros G name args tys ty H1 H2 H3 i j H4. simpl.
    rewrite H3. reflexivity. assumption.
  - intros G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G p q H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G p q H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G p q H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G p q H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G p H1 H2 i j H3. simpl. rewrite H2; try assumption. reflexivity.
  - intros G p H1 H2 i j H3. simpl.
    rewrite H2. reflexivity. apply le_n_S. assumption.
  - intros G p H1 H2 i j H3. simpl.
    rewrite H2. reflexivity. apply le_n_S. assumption.
  - intros G p H1 H2 i j H3. simpl.
    rewrite H2. reflexivity. apply le_n_S. assumption.
  - intros G A x H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G A p q H1 H2 H3 H4 H5 H6 i j H7. simpl.
    rewrite H2, H4, H6; try assumption. reflexivity.
  - intros G i j H1. reflexivity.
  - intros G t ts ty tys H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros G t H1 H2 i j H3. simpl. rewrite H2; try assumption. reflexivity.
  - intros G t H1 H2 i j H3. simpl. rewrite H2; try assumption. reflexivity.
  - intros G name args tys t H1 H2 H3 i j H4. simpl.
    rewrite H3. reflexivity. assumption.
  }
  destruct H1 as [H1 [H2 H3]].
  split.
  - intros G t ty i j H4 H5. apply (H1 G t ty); assumption.
  - split.
    + intros G ts tys i j H4 H5. apply (H2 G ts tys); assumption.
    + intros G p t i j H4 H5. apply (H3 G p t); assumption.
Qed.

(* Lifting above a checked term leaves it unchanged.                            *)
Proposition AboveT : forall (E:Env) (G:Ctx) (t:Term) (ty:Ty) (i j:nat),
  CheckT E G t ty -> length G <= i ->
  Shift.fromT i j t = t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.

(* Lifting above checked term arguments leaves them unchanged.                  *)
Proposition AboveTs : forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty)
  (i j:nat),
  CheckTs E G ts tys -> length G <= i ->
  Shift.fromTs i j ts = ts.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.

(* Lifting above a checked proof leaves it unchanged.                           *)
Proposition AboveP : forall (E:Env) (G:Ctx) (p:Proof) (t:Term) (i j:nat),
  CheckP E G p t -> length G <= i ->
  Shift.fromP i j p = p.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.

(* Weakening preserves checked objects across an inserted context.              *)
Proposition From : forall (E:Env),
  (forall (name:Name) (tys:list Ty) (t:Term),
    sigP E name = Some (tys,t) -> CheckT E (rev tys) t TyProp)            ->
  (forall (G M D:Ctx) (t:Term) (ty:Ty),
    CheckT E (G ++ D) t ty ->
    CheckT E (G ++ M ++ D) (Shift.fromT (length G) (length M) t) ty)      /\
  (forall (G M D:Ctx) (ts:Terms) (tys:list Ty),
    CheckTs E (G ++ D) ts tys ->
    CheckTs E (G ++ M ++ D) (Shift.fromTs (length G) (length M) ts) tys)  /\
  (forall (G M D:Ctx) (p:Proof) (t:Term),
    CheckP E (G ++ D) p t ->
    CheckP E (G ++ M ++ D) (Shift.fromP (length G) (length M) p)
      (Shift.fromT (length G) (length M) t)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E H1.
  assert (
    (forall (C:Ctx) (t:Term) (ty:Ty), CheckT E C t ty ->
      forall (G M D:Ctx), C = G ++ D ->
      CheckT E (G ++ M ++ D) (Shift.fromT (length G) (length M) t) ty)    /\
    (forall (C:Ctx) (ts:Terms) (tys:list Ty), CheckTs E C ts tys ->
      forall (G M D:Ctx), C = G ++ D ->
      CheckTs E (G ++ M ++ D) (Shift.fromTs (length G) (length M) ts) tys)/\
    (forall (C:Ctx) p (t:Term), CheckP E C p t ->
      forall (G M D:Ctx), C = G ++ D ->
      CheckP E (G ++ M ++ D) (Shift.fromP (length G) (length M) p)
        (Shift.fromT (length G) (length M) t))) as H2. {
    apply Induction.
    - intros C G M D H2. subst. apply CheckBot.
    - intros C G M D H2. subst. apply CheckTop.
    - intros C n ty H2 G M D H3. subst. apply VarT. assumption.
    - intros C ty G M D H2. subst. apply CheckHoleT.
    - intros C name args tys ty H2 H3 H4 G M D H5. subst. simpl.
      apply CheckIdentT with (tys := tys). 1: assumption. apply H4. reflexivity.
    - intros C x y H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckElem; [apply H3|apply H5]; reflexivity.
    - intros C x y H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckLeq; [apply H3|apply H5]; reflexivity.
    - intros C x y H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckGeq; [apply H3|apply H5]; reflexivity.
    - intros C x y H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckLt; [apply H3|apply H5]; reflexivity.
    - intros C x y H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckGt; [apply H3|apply H5]; reflexivity.
    - intros C x y H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckEqual; [apply H3|apply H5]; reflexivity.
    - intros C x y H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckNotEq; [apply H3|apply H5]; reflexivity.
    - intros C p q H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckImp; [apply H3|apply H5]; reflexivity.
    - intros C p q H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckIff; [apply H3|apply H5]; reflexivity.
    - intros C p q H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckAnd; [apply H3|apply H5]; reflexivity.
    - intros C p q H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckOr; [apply H3|apply H5]; reflexivity.
    - intros C p H2 H3 G M D H4. subst. simpl.
      apply CheckNot. apply H3. reflexivity.
    - intros C p H2 H3 G M D H4. subst. simpl.
      apply CheckAll. apply (H3 (TySet :: G) M D). reflexivity.
    - intros C p H2 H3 G M D H4. subst. simpl.
      apply CheckEx. apply (H3 (TySet :: G) M D). reflexivity.
    - intros C p H2 H3 G M D H4. subst. simpl.
      apply CheckLam. apply (H3 (TySet :: G) M D). reflexivity.
    - intros C A x H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckApp; [apply H3|apply H5]; reflexivity.
    - intros C A p q H2 H3 H4 H5 H6 H7 G M D H8. subst. simpl.
      apply CheckDef.
      + apply H3. reflexivity.
      + assert (CheckP E (G ++ M ++ D) (Shift.fromP (length G) (length M) p)
          (Shift.fromT (length G) (length M) (Exists A))) as H8. {
          apply H5. reflexivity. }
        rewrite Exists.FromT in H8. assumption.
      + assert (CheckP E (G ++ M ++ D) (Shift.fromP (length G) (length M) q)
          (Shift.fromT (length G) (length M) (Unique A))) as H8. {
          apply H7. reflexivity. }
        rewrite Unique.FromT in H8. assumption.
    - intros C G M D H2. subst. simpl. apply CheckTsNil.
    - intros C t ts ty tys H2 H3 H4 H5 G M D H6. subst. simpl.
      apply CheckTsCons; [apply H3|apply H5]; reflexivity.
    - intros C t H2 H3 G M D H4. subst. simpl.
      apply CheckHoleP. apply H3. reflexivity.
    - intros C t H2 H3 G M D H4. subst. simpl.
      apply CheckAxiomP. apply H3. reflexivity.
    - intros C name args tys t H2 H3 H4 G M D H5. subst. simpl.
      rewrite Apply.CommShiftT.
      assert (Shift.fromT (length G + lengthT args) (length M) t = t) as H5. {
        apply (AboveT E (rev tys) t TyProp).
        - apply (H1 name). assumption.
        - rewrite length_rev.
          assert (lengthT args = length tys) as H5. { apply (Length E (G ++ D)); assumption. }
          rewrite <- H5. rewrite Nat.add_comm. apply Nat.le_add_r. }
      rewrite H5.
      apply CheckIdentP with (tys := tys). 1: assumption. apply H4. reflexivity.
  }
  destruct H2 as [H2 [H3 H4]].
  split.
  - intros G M D t ty H5. apply (H2 (G ++ D) t ty); try assumption. reflexivity.
  - split.
    + intros G M D ts tys H5. apply (H3 (G ++ D) ts tys); try assumption. reflexivity.
    + intros G M D p t H5. apply (H4 (G ++ D) p t); try assumption. reflexivity.
Qed.

(* Weakening preserves checked terms across an inserted context.                *)
Proposition FromT : forall (E:Env),
  (forall (name:Name) (tys:list Ty) (t:Term),
    sigP E name = Some (tys,t) -> CheckT E (rev tys) t TyProp)            ->
  forall (G M D:Ctx) (t:Term) (ty:Ty),
    CheckT E (G ++ D) t ty ->
    CheckT E (G ++ M ++ D) (Shift.fromT (length G) (length M) t) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

(* Weakening preserves checked term arguments across an inserted context.       *)
Proposition FromTs : forall (E:Env),
  (forall (name:Name) (tys:list Ty) (t:Term),
    sigP E name = Some (tys,t) -> CheckT E (rev tys) t TyProp)            ->
  forall (G M D:Ctx) (ts:Terms) (tys:list Ty),
    CheckTs E (G ++ D) ts tys ->
    CheckTs E (G ++ M ++ D) (Shift.fromTs (length G) (length M) ts) tys.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

(* Weakening preserves checked proofs across an inserted context.               *)
Proposition FromP : forall (E:Env),
  (forall (name:Name) (tys:list Ty) (t:Term),
    sigP E name = Some (tys,t) -> CheckT E (rev tys) t TyProp)            ->
  forall (G M D:Ctx) (p:Proof) (t:Term),
    CheckP E (G ++ D) p t ->
    CheckP E (G ++ M ++ D) (Shift.fromP (length G) (length M) p)
      (Shift.fromT (length G) (length M) t).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

