Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Well-sorted term arguments have the same length as their sort list.          *)
Proposition Length : forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty),
  CheckTs E G ts tys                         ->
  lengthT ts = List.length tys.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G ts tys H1.
  induction H1 as [G|G t ts ty tys H1 H2 IH]. 1: reflexivity.
  unfold lengthT. unfold lengthT in IH. simpl. rewrite IH. reflexivity.
Qed.

(* The first term in well-sorted non-empty arguments has the first sort.        *)
Proposition Head :
  forall (E:Env) (G:Ctx) (t:Term) (ts:Terms) (ty:Ty) (tys:list Ty),
    CheckTs E G (ConsT t ts) (ty :: tys)     ->
    CheckT E G t ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G t ts ty tys H1.
  inversion H1. subst. assumption.
Qed.

(* The tail of well-sorted non-empty arguments is well sorted.                  *)
Proposition Tail :
  forall (E:Env) (G:Ctx) (t:Term) (ts:Terms) (ty:Ty) (tys:list Ty),
    CheckTs E G (ConsT t ts) (ty :: tys)     ->
    CheckTs E G ts tys.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G t ts ty tys H1.
  inversion H1. subst. assumption.
Qed.

(* Appending well-sorted term arguments preserves matching sorts.               *)
Proposition App :
  forall (E:Env) (G:Ctx) (ts us:Terms) (tys uys:list Ty),
    CheckTs E G ts tys                       ->
    CheckTs E G us uys                       ->
    CheckTs E G (appT ts us) (tys ++ uys).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G ts us tys uys H1.
  revert us uys.
  (* The proof follows the checked prefix; the empty prefix adds nothing.       *)
  induction H1 as [G|G t ts ty tys H1 H2 IH]; intros us uys H3. 1: assumption.
  (* Matching heads remain matching heads after appending the same suffixes.    *)
  apply CheckTsCons. assumption. apply IH. assumption.
Qed.

(* Reversing well-sorted term arguments preserves matching sorts.               *)
Proposition Rev :
  forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty),
    CheckTs E G ts tys                       ->
    CheckTs E G (revT ts) (rev tys).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G ts tys H1.
  (* The empty checked list remains empty after reversal.                       *)
  induction H1 as [G|G t ts ty tys H1 H2 IH]. 1: apply CheckTsNil.
  (* Reversal moves the checked head to the end of the checked reversed tail.   *)
  assert (revT (ConsT t ts) = appT (revT ts) (ConsT t NilT)) as H3. {
    reflexivity.
  }
  assert (rev (ty :: tys) = List.app (rev tys) [ty]) as H4. { reflexivity. }
  rewrite H3, H4. apply App. 1: assumption.
  apply CheckTsCons. 1: assumption. apply CheckTsNil.
Qed.

(* Matching entries in well-sorted term arguments have matching sorts.          *)
Proposition Nth :
  forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty) (n:nat) (t:Term) (ty:Ty),
    CheckTs E G ts tys                       ->
    nthT ts n = Some t                       ->
    nth_error tys n = Some ty                ->
    CheckT E G t ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G ts tys n t ty H1.
  revert n t ty.
  induction H1 as [G|G t' ts ty' tys H1 H2 IH]; intros n t ty H3 H4.
  - destruct n as [|n]; discriminate.
  - destruct n as [|n].
    + inversion H3. subst. inversion H4. subst. assumption.
    + apply IH with n; assumption.
Qed.

(* A selected checked term has the sort found in the unreversed sort list.      *)
Proposition ArgT :
  forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty) (n:nat) (ty:Ty),
    CheckTs E G ts (rev tys)                 ->
    nth_error tys n = Some ty                ->
    CheckT E G (argT ts n) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G ts tys n ty H1 H2.
  assert (CheckTs E G (revT ts) tys) as H3. {
    (* Reversing the checked terms also reverses the reversed sort list.        *)
    assert (rev (rev tys) = tys) as H3. { apply rev_involutive. }
    rewrite <- H3. apply Rev. assumption.
  }
  unfold argT.
  (* If the reversed term lookup succeeds, it matches the unreversed sort list. *)
  destruct (nthT (revT ts) n) as [t|] eqn:H4.
  - apply (Nth E G (revT ts) tys n); assumption.
    (* If the term lookup failed, the matching sort lookup would fail too.      *)
  - unfold nthT in H4.
    assert (lengthT (revT ts) = List.length tys) as H5. {
      apply Length with E G. assumption.
    }
    assert (nth_error tys n = None) as H6. {
      apply nth_error_None. rewrite <- H5. apply nth_error_None. assumption.
    }
    rewrite H2 in H6. discriminate.
Qed.


