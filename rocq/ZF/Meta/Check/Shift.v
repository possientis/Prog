Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.CoreT.
Require Import ZF.Meta.Check.CoreP.
Require Import ZF.Meta.Check.Env.
Require Import ZF.Meta.Check.InductionT.
Require Import ZF.Meta.Check.InductionP.
Require Import ZF.Meta.Check.Ts.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Exists.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Small.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
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

(* Lifting above a checked term or argument list leaves it unchanged.           *)
Local Proposition Above :
  (forall (E:Env) (G:Ctx) (t:Term) (ty:Ty) (i j:nat),
    CheckT E G t ty                                                       ->
    length G <= i                                                         ->
    Shift.fromT i j t = t)                                                /\
  (forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty) (i j:nat),
    CheckTs E G ts tys                                                    ->
    length G <= i                                                         ->
    Shift.fromTs i j ts = ts).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (
    (forall (E:Env) (G:Ctx) (t:Term) (ty:Ty),
      CheckT E G t ty -> forall (i j:nat), length G <= i ->
      Shift.fromT i j t = t)                                            /\
    (forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty),
      CheckTs E G ts tys -> forall (i j:nat), length G <= i ->
      Shift.fromTs i j ts = ts)) as H. {
  apply InductionT.Induction.
  - intros E G i j H1. reflexivity.
  - intros E G i j H1. reflexivity.
  - intros E G n ty H1 i j H2. simpl.
    (* A checked variable is below the length of its context.                   *)
    assert (n < length G) as H3. { apply (TypeOf.LtLength G n ty). assumption. }
    assert (n < i) as H4. {
      apply Nat.lt_le_trans with (m := length G); assumption. }
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
  - intros E G A H1 H2 i j H3. simpl. rewrite H2; try assumption. reflexivity.
  - intros E G A H1 H2 i j H3. simpl. rewrite H2; try assumption. reflexivity.
  - intros E G i j H1. reflexivity.
  - intros E G t ts ty tys H1 H2 H3 H4 i j H5. simpl.
    rewrite H2, H4; try assumption. reflexivity. }
  destruct H as [H1 H2].
  split.
  - intros E G t ty i j H3 H4. apply (H1 E G t ty); assumption.
  - intros E G ts tys i j H3 H4. apply (H2 E G ts tys); assumption.
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
  intros E G p t i j H1 H2.
  destruct H1 as [G t H1|G t H1|G name args tys t H1 H3].
  - simpl. rewrite (AboveT E G t TyProp i j); try assumption. reflexivity.
  - simpl. rewrite (AboveT E G t TyProp i j); try assumption. reflexivity.
  - simpl. rewrite (AboveTs E G args tys i j); try assumption. reflexivity.
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
      CheckTs E (G ++ M ++ D) (Shift.fromTs (length G) (length M) ts) tys))
    as H2. {
    apply InductionT.Induction.
    - intros E C H1 G M D H2. subst. apply CheckBot.
    - intros E C H1 G M D H2. subst. apply CheckTop.
    - intros E C n ty H1 H2 G M D H3. subst. apply VarT. assumption.
    - intros E C ty H1 G M D H2. subst. apply CheckHoleT.
    - intros E C name args tys ty H1 H2 H3 H4 G M D H5. subst.
      apply CheckIdentT with (tys := tys). 1: assumption.
      apply H3. assumption. reflexivity.
    - intros E C x y H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckElem; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C x y H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckLeq; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C x y H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckGeq; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C x y H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckLt; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C x y H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckGt; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C x y H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckEqual; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C x y H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckNotEq; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C p q H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckImp; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C p q H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckIff; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C p q H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckAnd; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C p q H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckOr; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C p H1 H2 H3 G M D H4. subst.
      apply CheckNot. apply H2. assumption. reflexivity.
    - intros E C p H1 H2 H3 G M D H4. subst.
      apply CheckAll.
      apply H2 with (G := TySet :: G) (M := M) (D := D). assumption. reflexivity.
    - intros E C p H1 H2 H3 G M D H4. subst.
      apply CheckEx.
      apply H2 with (G := TySet :: G) (M := M) (D := D). assumption. reflexivity.
    - intros E C p H1 H2 H3 G M D H4. subst.
      apply CheckLam.
      apply H2 with (G := TySet :: G) (M := M) (D := D). assumption. reflexivity.
    - intros E C A x H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckApp; [apply H2|apply H4]; try assumption; reflexivity.
    - intros E C A H1 H2 H3 G M D H4. subst.
      apply CheckDef. apply H2. assumption. reflexivity.
    - intros E C A H1 H2 H3 G M D H4. subst.
      apply CheckFromC. apply H2. assumption. reflexivity.
    - intros E C H1 G M D H2. subst. apply CheckTsNil.
    - intros E C t ts ty tys H1 H2 H3 H4 H5 G M D H6. subst.
      apply CheckTsCons; [apply H2|apply H4]; try assumption; reflexivity. }
  destruct H2 as [H2 H3].
  assert (forall (E:Env) (C:Ctx) (p:Proof) (t:Term), CheckP E C p t     ->
    Check E                                                               ->
    forall (G M D:Ctx), C = G ++ D                                        ->
    CheckP E (G ++ M ++ D) (Shift.fromP (length G) (length M) p)
      (Shift.fromT (length G) (length M) t)) as H4. {
    remember (fun (E:Env) (C:Ctx) (t:Term) (ty:Ty) =>
      Check E -> forall (G M D:Ctx), C = G ++ D ->
      CheckT E (G ++ M ++ D) (Shift.fromT (length G) (length M) t) ty)
      as P eqn:HP.
    remember (fun (E:Env) (C:Ctx) (ts:Terms) (tys:list Ty) =>
      Check E -> forall (G M D:Ctx), C = G ++ D ->
      CheckTs E (G ++ M ++ D) (Shift.fromTs (length G) (length M) ts) tys)
      as Q eqn:HQ.
    remember (fun (E:Env) (C:Ctx) (p:Proof) (t:Term) =>
      Check E -> forall (G M D:Ctx), C = G ++ D ->
      CheckP E (G ++ M ++ D) (Shift.fromP (length G) (length M) p)
        (Shift.fromT (length G) (length M) t)) as R eqn:HR.
    assert (forall (E:Env) (C:Ctx) (p:Proof) (t:Term), CheckP E C p t ->
      R E C p t) as K1. {
      apply (InductionP.Induction P Q R).
      - rewrite HP. apply H2.
      - rewrite HQ. apply H3.
      - rewrite HP. rewrite HR. intros E C t H5 H6 H7 G M D H8. subst.
      apply CheckHoleP. apply H6. assumption. reflexivity.
    - rewrite HP. rewrite HR. intros E C t H5 H6 H7 G M D H8. subst.
      apply CheckAxiomP. apply H6. assumption. reflexivity.
    - rewrite HQ. rewrite HR. intros E C name args tys t H5 H6 H7 H8 G M D H9. subst.
      rewrite Apply.CommShiftT.
      assert (Shift.fromT (length G + lengthT args) (length M) t = t) as H9. {
        apply (AboveT E (rev tys) t TyProp).
        - apply (SigP E name); assumption.
        - rewrite length_rev.
          assert (lengthT args = length tys) as H9. {
            apply (Length E (G ++ D)); assumption. }
          rewrite <- H9. rewrite Nat.add_comm. apply Nat.le_add_r. }
      rewrite H9.
      apply CheckIdentP with (tys := tys). 1: assumption.
      apply H7. assumption. reflexivity. }
    rewrite HR in K1. apply K1. }
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

