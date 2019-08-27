Set Implicit Arguments.

Require Import set.
Require Import subset.
Require Import equiv.
Require Import subset_transitive.

Proposition equiv_transitive: forall (a b c:set),
  equiv a b -> equiv b c -> equiv a c.
Proof.
  intros a b c Hab Hbc.
  unfold equiv in Hab. unfold equiv in Hbc.
  elim Hab. clear Hab. intros Hab Hba.
  elim Hbc. clear Hbc. intros Hbc Hcb.
  unfold equiv. split.
  apply subset_transitive with (b:= b). exact Hab. exact Hbc.
  apply subset_transitive with (b:= b). exact Hcb. exact Hba.
Qed.

