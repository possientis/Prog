Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Ty.

Import ListNotations.

Definition Ctx : Type := list Ty.

Definition empty : Ctx := [].

Fixpoint typeOf (G:Ctx) (n:nat) : option Ty :=
  match G, n with
  | []        , _   => None
  | ty  :: _  , 0   => Some ty
  | _   :: H  , S n => typeOf H n
  end.

(* Context lookup agrees with list lookup.                                      *)
Proposition TypeOfNthError :
  forall (G:Ctx) (n:nat),
    typeOf G n = nth_error G n.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros G n.
  generalize dependent n.
  induction G as [|ty G IH]; intros n.
  - (* In the empty context, every lookup fails on both sides.                  *)
    destruct n as [|n]; reflexivity.
  - (* In a non-empty context, zero selects the head and successors descend.    *)
    destruct n as [|n]. 1: reflexivity.
    apply IH.
Qed.

(* A lookup remains valid after adding newer variables in front.                *)
Proposition TypeOfAppR :
  forall (G D:Ctx) (n:nat) (ty:Ty),
    typeOf D n = Some ty                      ->
    typeOf (G ++ D) (length G + n) = Some ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros G D n ty H1.
  induction G as [|ty' G IH]; assumption.
Qed.

(* A lookup in the front context is unchanged by adding older variables.        *)
Proposition TypeOfAppL :
  forall (G D:Ctx) (n:nat) (ty:Ty),
    typeOf G n = Some ty                      ->
    typeOf (G ++ D) n = Some ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros G D n ty H1.
  generalize dependent n.
  induction G as [|ty' G IH]; intros n H1.
  - discriminate.
  - destruct n as [|n].
    + rewrite <- H1. reflexivity.
    + apply IH. assumption.
Qed.

(* A lookup past a front context is a lookup in the older tail context.         *)
Proposition TypeOfAppSplitR :
  forall (D G:Ctx) (n:nat) (ty:Ty),
    length D <= n                             ->
    typeOf (D ++ G) n = Some ty               ->
    typeOf G (n - length D) = Some ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros D G n ty H1 H2.
  generalize dependent n.
  induction D as [|ty' D IH]; intros n H1 H2.
  - (* With no front context, the lookup is already in the tail context.        *)
    rewrite Nat.sub_0_r. assumption.
  - (* Successor indices past a non-empty front context descend through it.     *)
    destruct n as [|n].
    + inversion H1.
    + apply IH. 2: assumption.
      apply le_S_n. assumption.
Qed.

(* A successful lookup is within the length of its context.                     *)
Proposition TypeOfLtLength :
  forall (G:Ctx) (n:nat) (ty:Ty),
    typeOf G n = Some ty                      ->
    n < length G.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros G n ty H1.
  generalize dependent n.
  induction G as [|ty' G IH]; intros n H1.
  - discriminate.
  - destruct n as [|n].
    + apply le_n_S, Nat.le_0_l.
    + apply le_n_S, IH. assumption.
Qed.
