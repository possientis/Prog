Require Import ZF.Binary.
Require Import ZF.Core.Equal.

(* The converse of a binary class.                                              *)
Definition converse (F:Binary) : Binary := fun x y => F y x.

(* Taking the converse is an indempotent operation.                             *)
(* Note that we have actual equality here, not just equivalence.                *)
Proposition ConverseIdempotent : forall (F:Binary),
  converse (converse F) = F.
Proof.
  intros F. unfold converse. reflexivity.
Qed.

(* The converse operation is compatible with equivalence.                       *)
Proposition ConverseEqualCompat : EqualCompat converse.
Proof.
  intros F G H1 x y. unfold converse. apply H1.
Qed.
