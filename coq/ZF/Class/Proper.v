Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.

(* Predicate on classes, determining whether a class is proper.                 *)
Definition Proper (P:Class) : Prop := ~Small P.

(* A proper class is non-empty.                                                 *)
Proposition IsNotEmpty : forall (A:Class), Proper A -> A :<>: :0:.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A H1 H2.
  (* The empty class is small; A is small by equivalence, contradiction         *)
  apply H1.
  apply Small.EquivCompat with :0:.
  - apply Equiv.Sym. assumption.
  - apply Empty.IsSmall.
Qed.
