Lemma L1: 6*6 = 9*4.
Proof.
  reflexivity.
Qed.

Require Import ZArith.
Open Scope Z_scope.

(* you cannot use 'reflexivity here', a b are free variables
unlike 6 9 4 and no reduction can take place, not unification *)

Lemma diff_of_squares : forall a b:Z, (a+b)*(a-b) = a*a - b*b.
Proof.
  intros. ring.
Qed.


Theorem eq_sym' : forall (A:Type)(a b :A), a = b -> b = a.
Proof.
  intros A a b H. rewrite -> H. reflexivity.
Qed.

Check Zmult_plus_distr_l. (* forall n m p : Z, (n + m) * p = n * p + m * p *)
Check Zmult_1_l.          (* forall n : Z, 1 * n = n *)

Theorem Zmult_distr_1 : forall n x:Z, n*x+x = (n+1)*x.
Proof.
  intros n x.
  (*
  ring.
  *)
  rewrite Zmult_plus_distr_l.
  rewrite Zmult_1_l.
  reflexivity.
Qed.

(* can also use 'rewrite ... in H', 'rewrite -> ... in H' or 'rewrite <- ... in H' *)


Theorem regroup : forall x:Z, x+x+x+x+x = 5*x.
Proof.
(*
  intro x. ring.
*)
  intro. pattern x at 1. rewrite <- Zmult_1_l.
  repeat rewrite Zmult_distr_1.
  reflexivity.
Qed.

Open Scope nat_scope.
Check plus_comm.  (* forall n m : nat, n + m = m + n *)
Check plus_assoc. (* forall n m p : nat, n + (m + p) = n + m + p *)

Theorem plus_permute2: forall n m p:nat, n+m+p = n+p+m.
Proof.
  intros n m p. rewrite <- plus_assoc. rewrite plus_comm with (n:=m)(m:=p). 
  rewrite plus_assoc. reflexivity.
Qed.

Lemma le_lt_S_eq : forall n p:nat, n <= p -> p < S n -> n = p.
Proof.
  intros n p. omega. (* we ll see this tactic later *)
Qed.

Check plus_lt_reg_l. (* forall n m p : nat, p + n < p + m -> n < m *)
Check plus_le_reg_l. (* forall n m p : nat, p + n <= p + m -> n <= m *)
Check plus_comm. (* forall n m : nat, n + m = m + n *)


Lemma cond_rewrite_example : forall n:nat,
  8 <= n+6 -> 3+n < 6 -> n*n = n+n.
Proof.
  intros n H0 H1.
  rewrite <- le_lt_S_eq with (p:=n)(n:=2).
  reflexivity.
  apply plus_le_reg_l with (p:=6).
  rewrite plus_comm with (n:=6)(m:=n). exact H0.
  apply plus_lt_reg_l with (p:=3). exact H1.
Qed.


Check eq_ind. (* forall (A : Type) (x : A) (P : A -> Prop),
                 P x -> forall y : A, x = y -> P y *)

Theorem eq_trans1 : forall (A:Type)(x y z:A), x = y -> y = z -> x = z.
Proof.
  intros A x y z eq_xy eq_yz. 
  apply eq_ind with (y:=z)(x:=y)(P:= fun u => x = u).
  exact eq_xy. exact eq_yz.
Qed.

Theorem eq_trans2 : forall (A:Type)(x y z:A), x = y -> y = z -> x = z.
Proof.
  intros A x y z eq_xy eq_yz.
  rewrite <- eq_yz. exact eq_xy.
Qed.

Check Zmult_1_l. (* forall n : Z, (1 * n)%Z = n *)
SearchRewrite (1 * _).
(*
mult_1_l: forall n : nat, 1 * n = n
*)

SearchRewrite (1 * _)%Z. (* fail *)

Open Scope Z_scope.
SearchRewrite (1 * _). (* fail *)










