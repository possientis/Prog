Require Import Arith ZArith.
Open Scope nat_scope.
Set Implicit Arguments.

Check le.
Check lt.
Print lt. (* lt = fun n m : nat => S n <= m : nat -> nat -> Prop *)

Theorem conv_example : forall n:nat, 7*5 < n -> 6*6 <= n.
Proof.
  intros n H.
  exact H. (* the tactic 'exact' will succeed provided type conversion is possible *)
  (* the same it true of 'assumption' *)
Qed.
(* although the terms 7*5 < n and 6*6 <= n are different, following delta , iota and beta reductions, both terms are reduced to 36 <= n and consequently 
the tactics 'exact H' or 'assumption' will succeed *)


Lemma L_35_36 : forall n:nat, 7*5 < n -> 6*6 <= n.
Proof.
  intro n.
  intro H.
  exact H.
Qed.

Print L_35_36. (* proof is very simple, conversion rules enable hiding arithmetic calculations linked to '*' *)

Theorem implication_transitive:
  forall P Q R : Prop, (P->Q)->(Q->R)->P->R.
Proof.
  intros P Q R Hpq Hqr Hp.
  apply Hqr; apply Hpq; exact Hp.
Qed.

Print implication_transitive.

Check (implication_transitive (le_S 0 1) (le_S 0 2)).

Definition neutral_left (A:Set)(op:A->A->A)(e:A) : Prop :=
  forall x:A, op e x = x.

Theorem one_neutral_left : neutral_left Zmult 1%Z.
Proof.
  intro z. (* current goal not a dependent product, but reducible to one, so intro succeeds *)
  auto with zarith.
Qed.

Check le_n.
Print le_n.

Definition nope := False.

Check nope. (* Prop, defining nope to False does not prove False *)
(* proving False requires finding a proof term of type False *)

Check le_S.
Check le_trans.

Lemma L1: 33 <= 34.
Proof.
  apply le_S.
  apply le_n.
Qed.


Theorem le_i_SSi : forall i:nat, i <= S (S i).
Proof.
  intro i.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Theorem forall_implication_distributivity:
  forall (A:Type)(P Q: A->Prop), 
  (forall x:A, P x -> Q x) -> (forall x:A, P x) -> (forall x:A, Q x).
Proof.
  intros A P Q H Hp x.
  apply H.
  apply Hp.
Qed.


Check le_trans.
Check mult_le_compat_l.
Check mult_le_compat_r.

Theorem le_mult_mult : forall a b c d: nat,
  a <= c -> b <= d -> a*b <= c*d.
Proof.
  intros a b c d Hac Hbd.
(*  apply le_trans. *) (* Error: Unable to find an instance for the variable m. *)
  (* apply with *)
  apply le_trans with (m := c*b). (* apply t with (v1 := t1)(v2 := t2)...(vk := tk)
  apply mult_le_compat_r.
  exact Hac.
  apply mult_le_compat_l.
  exact Hbd.
Qed.

















