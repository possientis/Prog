Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.Env.
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
Proposition Above :
  (forall (E:Env) (G:Ctx) (t:Term) (ty:Ty) (i j:nat),
    CheckT E G t ty                                                       ->
    length G <= i                                                         ->
    Shift.fromT i j t = t)                                                /\
  (forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty) (i j:nat),
    CheckTs E G ts tys                                                    ->
    length G <= i                                                         ->
    Shift.fromTs i j ts = ts)                                             /\
  (forall (E:Env) (G:Ctx) (p:Proof) (t:Term) (i j:nat),
    CheckP E G p t                                                        ->
    length G <= i                                                         ->
    Shift.fromP i j p = p).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (
    (forall (E:Env) (G:Ctx) (t:Term) (ty:Ty),
      CheckT E G t ty -> forall (i j:nat), length G <= i ->
      Shift.fromT i j t = t)                                            /\
    (forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty),
      CheckTs E G ts tys -> forall (i j:nat), length G <= i ->
      Shift.fromTs i j ts = ts)                                         /\
    (forall (E:Env) (G:Ctx) (p:Proof) (t:Term),
      CheckP E G p t -> forall (i j:nat), length G <= i ->
      Shift.fromP i j p = p)) as H. {
  apply Induction.
  - intros E G i j H1. reflexivity.
  - intros E G i j H1. reflexivity.
  - intros E G n ty H1 i j H2. simpl.
    (* A checked variable is below the length of its context.                   *)
    assert (n < length G) as H3. { apply (TypeOf.LtLength G n ty). assumption. }
    assert (n < i) as H4. { apply Nat.lt_le_trans with (m := length G); assumption. }
    assert ((n <? i) = true) as H5. { apply Nat.ltb_lt. assumption. }
    rewrite H5. reflexivity.
  - intros E G ty i j H1. reflexivity.
  - intros E G name args tys ty H1 H2 H3 i j H4. simpl.
    rewrite H3. reflexivity. assumption.
  - intros E G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G x y H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G p q H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G p q H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G p q H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G p q H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G p H1 H2 i j H3. simpl. rewrite H2; try assumption. reflexivity.
  - intros E G p H1 H2 i j H3. simpl.
    rewrite H2. reflexivity. apply le_n_S. assumption.
  - intros E G p H1 H2 i j H3. simpl.
    rewrite H2. reflexivity. apply le_n_S. assumption.
  - intros E G p H1 H2 i j H3. simpl.
    rewrite H2. reflexivity. apply le_n_S. assumption.
  - intros E G A x H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G A p q H1 H2 H3 H4 H5 H6 i j H7. simpl.
    rewrite H2, H4, H6; try assumption. reflexivity.
  - intros E G i j H1. reflexivity.
  - intros E G t ts ty tys H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity.
  - intros E G t H1 H2 i j H3. simpl. rewrite H2; try assumption. reflexivity.
  - intros E G t H1 H2 i j H3. simpl. rewrite H2; try assumption. reflexivity.
  - intros E G name args tys t H1 H2 H3 i j H4. simpl.
    rewrite H3; try assumption. reflexivity. }
  destruct H as [H [H0 H00]].
  split.
  - intros E G t ty i j H1 H2. apply (H E G t ty); assumption.
  - split.
    + intros E G ts tys i j H1 H2. apply (H0 E G ts tys); assumption.
    + intros E G p t i j H1 H2. apply (H00 E G p t); assumption.
Qed.

(* Lifting above a checked term leaves it unchanged.                            *)
Proposition AboveT : forall (E:Env) (G:Ctx) (t:Term) (ty:Ty)(i j:nat),
  CheckT E G t ty                                                         ->
  length G <= i                                                           ->
  Shift.fromT i j t = t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.

(* Lifting above checked term arguments leaves them unchanged.                  *)
Proposition AboveTs : forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty) (i j:nat),
  CheckTs E G ts tys                                                      ->
  length G <= i                                                           ->
  Shift.fromTs i j ts = ts.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.

(* Lifting above a checked proof leaves it unchanged.                           *)
Proposition AboveP : forall (E:Env) (G:Ctx) (p:Proof) (t:Term) (i j:nat),
  CheckP E G p t                                                          ->
  length G <= i                                                           ->
  Shift.fromP i j p = p.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Above.
Qed.

(* Proof signature conclusions are unchanged by lifting above their parameters. *)
Proposition SigPAbove : forall (E:Env) (name:Name) (tys:list Ty) (t:Term)
  (i j:nat),
  Check E                       ->
  sigP E name = Some (tys,t)    ->
  length tys <= i               ->
  Shift.fromT i j t = t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E name tys t i j H1 H2 H3.
  assert (CheckT E (rev tys) t TyProp) as H4. {
    apply (SigP E name); assumption. }
  apply (AboveT E (rev tys) t TyProp); try assumption.
  rewrite length_rev. assumption.
Qed.

(* Weakening preserves checked objects across an inserted context.              *)
Proposition From :
  (forall (E:Env) (G M D:Ctx) (t:Term) (ty:Ty),
    Check E                                                               ->
    CheckT E (G ++ D) t ty                                                ->
    CheckT E (G ++ M ++ D) (Shift.fromT (length G) (length M) t) ty)      /\
  (forall (E:Env) (G M D:Ctx) (ts:Terms) (tys:list Ty),
    Check E                                                               ->
    CheckTs E (G ++ D) ts tys                                             ->
    CheckTs E (G ++ M ++ D) (Shift.fromTs (length G) (length M) ts) tys)  /\
  (forall (E:Env) (G M D:Ctx) (p:Proof) (t:Term),
    Check E                                                               ->
    CheckP E (G ++ D) p t                                                 ->
    CheckP E (G ++ M ++ D) (Shift.fromP (length G) (length M) p)
      (Shift.fromT (length G) (length M) t)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (
    (forall (E:Env) (C:Ctx) (t:Term) (ty:Ty), CheckT E C t ty             ->
      Check E                                                             ->
      forall (G M D:Ctx), C = G ++ D                                      ->
      CheckT E (G ++ M ++ D) (Shift.fromT (length G) (length M) t) ty)    /\
    (forall (E:Env) (C:Ctx) (ts:Terms) (tys:list Ty), CheckTs E C ts tys  ->
      Check E                                                             ->
      forall (G M D:Ctx), C = G ++ D                                      ->
      CheckTs E (G ++ M ++ D) (Shift.fromTs (length G) (length M) ts) tys)/\
    (forall (E:Env) (C:Ctx) p (t:Term), CheckP E C p t                    ->
      Check E                                                             ->
      forall (G M D:Ctx), C = G ++ D                                      ->
      CheckP E (G ++ M ++ D) (Shift.fromP (length G) (length M) p)
        (Shift.fromT (length G) (length M) t))) as H2. {
    apply Induction.
    - intros E C H2 G M D H3. subst. apply CheckBot.
    - intros E C H2 G M D H3. subst. apply CheckTop.
    - intros E C n ty H2 H3 G M D H4. subst. apply VarT. assumption.
    - intros E C ty H2 G M D H3. subst. apply CheckHoleT.
    - intros E C name args tys ty H2 H3 H4 H5 G M D H6. subst.
      apply CheckIdentT with (tys := tys). 1: assumption.
      apply H4. assumption. reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckElem; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckLeq; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckGeq; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckLt; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckGt; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckEqual; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C x y H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckNotEq; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C p q H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckImp; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C p q H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckIff; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C p q H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckAnd; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C p q H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckOr; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C p H2 H3 H4 G M D H5. subst.
      apply CheckNot. apply H3. assumption. reflexivity.
    - intros E C p H2 H3 H4 G M D H5. subst.
      apply CheckAll.
      apply H3 with (G := TySet :: G) (M := M) (D := D). assumption. reflexivity.
    - intros E C p H2 H3 H4 G M D H5. subst.
      apply CheckEx.
      apply H3 with (G := TySet :: G) (M := M) (D := D). assumption. reflexivity.
    - intros E C p H2 H3 H4 G M D H5. subst.
      apply CheckLam.
      apply H3 with (G := TySet :: G) (M := M) (D := D). assumption. reflexivity.
    - intros E C A x H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckApp; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C A p q H2 H3 H4 H5 H6 H7 H8 G M D H9. subst.
      apply CheckDef.
      + apply H3. assumption. reflexivity.
      + rewrite <- Exists.ShiftT. apply H5. assumption. reflexivity.
      + rewrite <- Unique.ShiftT. apply H7. assumption. reflexivity.
    - intros E C H2 G M D H3. subst. apply CheckTsNil.
    - intros E C t ts ty tys H2 H3 H4 H5 H6 G M D H7. subst.
      apply CheckTsCons; [apply H3|apply H5]; try assumption; reflexivity.
    - intros E C t H2 H3 H4 G M D H5. subst.
      apply CheckHoleP. apply H3. assumption. reflexivity.
    - intros E C t H2 H3 H4 G M D H5. subst.
      apply CheckAxiomP. apply H3. assumption. reflexivity.
    - intros E C name args tys t H2 H3 H4 H5 G M D H6. subst.
      rewrite Apply.CommShiftT.
      assert (Shift.fromT (length G + lengthT args) (length M) t = t) as H6. {
        apply (AboveT E (rev tys) t TyProp).
        - apply (SigP E name); assumption.
        - rewrite length_rev.
          assert (lengthT args = length tys) as H6. {
            apply (Length E (G ++ D)); assumption. }
          rewrite <- H6. rewrite Nat.add_comm. apply Nat.le_add_r. }
      rewrite H6.
      apply CheckIdentP with (tys := tys). 1: assumption.
      apply H4. assumption. reflexivity. }
  destruct H2 as [H2 [H3 H4]].
  split.
  - intros E G M D t ty H1 H5.
    apply (H2 E (G ++ D) t ty); try assumption. reflexivity.
  - split.
    + intros E G M D ts tys H1 H5.
      apply (H3 E (G ++ D) ts tys); try assumption. reflexivity.
    + intros E G M D p t H1 H5.
      apply (H4 E (G ++ D) p t); try assumption. reflexivity.
Qed.

(* Weakening preserves checked terms across an inserted context.                *)
Proposition FromT : forall (E:Env),
  forall (G M D:Ctx) (t:Term) (ty:Ty),
    Check E                                                               ->
    CheckT E (G ++ D) t ty                                                ->
    CheckT E (G ++ M ++ D) (Shift.fromT (length G) (length M) t) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

(* Weakening preserves checked term arguments across an inserted context.       *)
Proposition FromTs : forall (E:Env),
  forall (G M D:Ctx) (ts:Terms) (tys:list Ty),
    Check E                                                               ->
    CheckTs E (G ++ D) ts tys                                             ->
    CheckTs E (G ++ M ++ D) (Shift.fromTs (length G) (length M) ts) tys.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

(* Weakening preserves checked proofs across an inserted context.               *)
Proposition FromP : forall (E:Env),
  forall (G M D:Ctx) (p:Proof) (t:Term),
    Check E                                                               ->
    CheckP E (G ++ D) p t                                                 ->
    CheckP E (G ++ M ++ D) (Shift.fromP (length G) (length M) p)
      (Shift.fromT (length G) (length M) t).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply From.
Qed.

