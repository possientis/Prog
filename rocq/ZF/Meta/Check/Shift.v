Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.Induction.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.TypeOf.
Require Import ZF.Meta.Ty.

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

