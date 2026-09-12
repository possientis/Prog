Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.Env.
Require Import ZF.Meta.Check.Induction.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.TypeOf.
Require Import ZF.Meta.Ty.

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
