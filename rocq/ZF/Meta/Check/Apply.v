Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.Ts.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
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
