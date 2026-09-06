Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Ty.

Import ListNotations.

Fixpoint typeOf (G:Ctx) (n:nat) : option Ty :=
  match G, n with
  | []        , _   => None
  | ty  :: _  , 0   => Some ty
  | _   :: H  , S n => typeOf H n
  end.

(* Context lookup agrees with list lookup.                                      *)
Proposition NthError :
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

(* A lookup in the front context is unchanged by adding older variables.        *)
Proposition AppL :
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

(* A lookup remains valid after adding newer variables in front.                *)
Proposition AppR :
  forall (G D:Ctx) (n:nat) (ty:Ty),
    typeOf D n = Some ty                      ->
    typeOf (G ++ D) (length G + n) = Some ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros G D n ty H1.
  induction G as [|ty' G IH]; assumption.
Qed.

(* A lookup before the end of a front context is a lookup in that context.      *)
Proposition AppSplitL :
  forall (G D:Ctx) (n:nat) (ty:Ty),
    n < length G                              ->
    typeOf (G ++ D) n = Some ty               ->
    typeOf G n = Some ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros G D n ty H1 H2.
  generalize dependent n.
  induction G as [|ty' G IH]; intros n H1 H2.
  - (* No lookup can lie before the end of the empty context.                   *)
    inversion H1.
  - (* At the head, the combined lookup is exactly the front lookup.            *)
    destruct n as [|n].
    + rewrite <- H2. reflexivity.
    + (* Past the head, both lookups descend to the remaining front context.    *)
      apply IH. 2: assumption.
      apply le_S_n. assumption.
Qed.

(* A lookup past a front context is a lookup in the older tail context.         *)
Proposition AppSplitR :
  forall (G D:Ctx) (n:nat) (ty:Ty),
    length G <= n                             ->
    typeOf (G ++ D) n = Some ty               ->
    typeOf D (n - length G) = Some ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros G D n ty H1 H2.
  generalize dependent n.
  induction G as [|ty' G IH]; intros n H1 H2.
  - (* With no front context, the lookup is already in the tail context.        *)
    rewrite Nat.sub_0_r. assumption.
  - (* Successor indices past a non-empty front context descend through it.     *)
    destruct n as [|n].
    + inversion H1.
    + apply IH. 2: assumption.
      apply le_S_n. assumption.
Qed.

(* A successful lookup is within the length of its context.                     *)
Proposition LtLength :
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
