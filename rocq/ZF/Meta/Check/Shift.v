Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Check.Core.
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
