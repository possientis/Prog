Declare Scope ZF_Binary_Restrict_scope.
Open    Scope ZF_Binary_Restrict_scope.

Require Import ZF.Binary.
Require Import ZF.Binary.Image.
Require Import ZF.Binary.Range.
Require Import ZF.Class.
Require Import ZF.Set.

(* Restricting a binary class F to a class P.                                   *)
Definition restrict (F:Binary) (P:Class) : Binary := fun x y =>
  P x /\ F x y.

Notation "F :|: P" := (restrict F P)
  (at level 13, left associativity) : ZF_Binary_Restrict_scope.

(* Image is the range of the restriction.                                       *)
(* This is an equal equality, not just equivalence.                             *)
Proposition ImageIsRestriction : forall (F:Binary) (a:U),
  F:[a]: = range (F:|: (toClass a)).
Proof.
  intros F a. unfold image, range, restrict. reflexivity.
Qed.
