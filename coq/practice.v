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
  apply le_trans with (m := c*b). (* apply t with (v1 := t1)(v2 := t2)...(vk := tk) *)
  apply mult_le_compat_r.
  exact Hac.
  apply mult_le_compat_l.
  exact Hbd.
Qed.


(* the tatic eapply *)
Theorem le_mult_mult' : forall a b c d: nat,
  a <= c -> b <= d -> a*b <= c*d.
Proof.
  intros a b c d Hac Hbd.
  eapply le_trans.
  eapply mult_le_compat_l.
  eexact Hbd. (* exact Hbd will also work here *)
  apply mult_le_compat_r.
  exact Hac.
Qed.


Theorem le_0_mult_l : forall n p:nat, 0*n <= 0*p.
Proof.
  intros n p; apply le_n. (* comparison of terms for tactics do take reducibility into account *)
  (* both 0*n and 0*p reduce to 0, so goal actuall 0 <= 0, which is handled by le_n *) 
Qed.

(* n*0 and p*0 are not reducible to 0 for some reason *)
Theorem le_0_mult_r : forall n p:nat, n*0 <= p*0.
Proof.
  intros n p.
  (*  apply le_n. will fail here *)
  cut (0*n = n*0).
  cut (0*p = p*0).
  intros Hp Hn.
  rewrite <- Hn.
  rewrite <- Hp.
  apply le_0_mult_l.
  apply mult_comm.
  apply mult_comm.
Qed.

Lemma lt_8_9 : 8 < 9.
Proof.
  apply le_n. (* delta reduction does take place to le_n does succeed *)
Qed.

(* Search command very useful *)

Open Scope Z_scope. (* this will make output of Search a lot nicer *)
Check Zle. (* Z -> Z -> Prop *)
Search Zle.
(*
log_sup_le_Slog_inf: forall p : positive, log_sup p <= Z.succ (log_inf p)
log_sup_correct1: forall p : positive, 0 <= log_sup p
log_near_correct1: forall p : positive, 0 <= log_near p
log_inf_le_log_sup: forall p : positive, log_inf p <= log_sup p
log_inf_correct1: forall p : positive, 0 <= log_inf p
inj_le: forall n m : nat, (n <= m)%nat -> Z.of_nat n <= Z.of_nat m
Zsucc_le_reg: forall n m : Z, Z.succ m <= Z.succ n -> m <= n
Zsucc_le_compat: forall n m : Z, m <= n -> Z.succ m <= Z.succ n
Zplus_le_reg_r: forall n m p : Z, n + p <= m + p -> n <= m
Zplus_le_reg_l: forall n m p : Z, p + n <= p + m -> n <= m
Zplus_le_compat_r: forall n m p : Z, n <= m -> n + p <= m + p
Zplus_le_compat_l: forall n m p : Z, n <= m -> p + n <= p + m
Znot_gt_le: forall n m : Z, ~ n > m -> n <= m
Zmult_lt_0_le_reg_r: forall n m p : Z, 0 < p -> n * p <= m * p -> n <= m
Zmult_lt_0_le_compat_r: forall n m p : Z, 0 < p -> n <= m -> n * p <= m * p
Zmult_le_reg_r: forall n m p : Z, p > 0 -> n * p <= m * p -> n <= m
Zmult_le_compat_r: forall n m p : Z, n <= m -> 0 <= p -> n * p <= m * p
Zmult_le_compat_l: forall n m p : Z, n <= m -> 0 <= p -> p * n <= p * m
Zmult_le_compat: forall n m p q : Z, n <= p -> m <= q -> 0 <= n -> 0 <= m -> n * m <= p * q
Zmult_le_approx: forall n m p : Z, n > 0 -> n > p -> 0 <= m * n + p -> 0 <= m
Zmult_le_0_reg_r: forall n m : Z, n > 0 -> 0 <= m * n -> 0 <= m
Zmult_gt_0_le_compat_r: forall n m p : Z, p > 0 -> n <= m -> n * p <= m * p
Zmult_gt_0_le_0_compat: forall n m : Z, n > 0 -> 0 <= m -> 0 <= m * n
Zmod_le: forall a b : Z, 0 < b -> 0 <= a -> a mod b <= a
Zlt_succ_le: forall n m : Z, n < Z.succ m -> n <= m
Zlt_left: forall n m : Z, n < m -> 0 <= m + -1 + - n
Zlt_le_succ: forall n m : Z, n < m -> Z.succ n <= m
Zlt_0_le_0_pred: forall n : Z, 0 < n -> 0 <= Z.pred n
Zle_succ_le: forall n m : Z, Z.succ n <= m -> n <= m
Zle_neg_pos: forall p q : positive, Z.neg p <= Z.pos q
Zle_mult_approx: forall n m p : Z, n > 0 -> p > 0 -> 0 <= m -> 0 <= m * n + p
Zle_minus_le_0: forall n m : Z, m <= n -> 0 <= n - m
Zle_left_rev: forall n m : Z, 0 <= m + - n -> n <= m
Zle_left: forall n m : Z, n <= m -> 0 <= m + - n
Zle_bool_imp_le: forall n m : Z, (n <=? m) = true -> n <= m
Zle_0_pos: forall p : positive, 0 <= Z.pos p
Zle_0_nat: forall n : nat, 0 <= Z.of_nat n
Zle_0_minus_le: forall n m : Z, 0 <= n - m -> m <= n
Zgt_succ_le: forall n m : Z, Z.succ m > n -> n <= m
Zgt_left: forall n m : Z, n > m -> 0 <= n + -1 + - m
Zgt_le_succ: forall n m : Z, m > n -> Z.succ n <= m
Zgt_0_le_0_pred: forall n : Z, n > 0 -> 0 <= Z.pred n
log_sup_le_Slog_inf: forall p : positive, log_sup p <= Z.succ (log_inf p)
log_sup_correct1: forall p : positive, 0 <= log_sup p
log_near_correct1: forall p : positive, 0 <= log_near p
log_inf_le_log_sup: forall p : positive, log_inf p <= log_sup p
log_inf_correct1: forall p : positive, 0 <= log_inf p
inj_le: forall n m : nat, (n <= m)%nat -> Z.of_nat n <= Z.of_nat m
Zsucc_le_reg: forall n m : Z, Z.succ m <= Z.succ n -> m <= n
Zsucc_le_compat: forall n m : Z, m <= n -> Z.succ m <= Z.succ n
Zplus_le_reg_r: forall n m p : Z, n + p <= m + p -> n <= m
Zplus_le_reg_l: forall n m p : Z, p + n <= p + m -> n <= m
Zplus_le_compat_r: forall n m p : Z, n <= m -> n + p <= m + p
Zplus_le_compat_l: forall n m p : Z, n <= m -> p + n <= p + m
Znot_gt_le: forall n m : Z, ~ n > m -> n <= m
Zmult_lt_0_le_reg_r: forall n m p : Z, 0 < p -> n * p <= m * p -> n <= m
Zmult_lt_0_le_compat_r: forall n m p : Z, 0 < p -> n <= m -> n * p <= m * p
Zmult_le_reg_r: forall n m p : Z, p > 0 -> n * p <= m * p -> n <= m
Zmult_le_compat_r: forall n m p : Z, n <= m -> 0 <= p -> n * p <= m * p
Zmult_le_compat_l: forall n m p : Z, n <= m -> 0 <= p -> p * n <= p * m
Zmult_le_compat:
forall n m p q : Z, n <= p -> m <= q -> 0 <= n -> 0 <= m -> n * m <= p * q
Zmult_le_approx: forall n m p : Z, n > 0 -> n > p -> 0 <= m * n + p -> 0 <= m
Zmult_le_0_reg_r: forall n m : Z, n > 0 -> 0 <= m * n -> 0 <= m
Zmult_gt_0_le_compat_r: forall n m p : Z, p > 0 -> n <= m -> n * p <= m * p
Zmult_gt_0_le_0_compat: forall n m : Z, n > 0 -> 0 <= m -> 0 <= m * n
Zmod_le: forall a b : Z, 0 < b -> 0 <= a -> a mod b <= a
Zlt_succ_le: forall n m : Z, n < Z.succ m -> n <= m
Zlt_left: forall n m : Z, n < m -> 0 <= m + -1 + - n
Zlt_le_succ: forall n m : Z, n < m -> Z.succ n <= m
Zlt_0_le_0_pred: forall n : Z, 0 < n -> 0 <= Z.pred n
Zle_succ_le: forall n m : Z, Z.succ n <= m -> n <= m
Zle_neg_pos: forall p q : positive, Z.neg p <= Z.pos q
Zle_mult_approx: forall n m p : Z, n > 0 -> p > 0 -> 0 <= m -> 0 <= m * n + p
Zle_minus_le_0: forall n m : Z, m <= n -> 0 <= n - m
Zle_left_rev: forall n m : Z, 0 <= m + - n -> n <= m
Zle_left: forall n m : Z, n <= m -> 0 <= m + - n
Zle_bool_imp_le: forall n m : Z, (n <=? m) = true -> n <= m
Zle_0_pos: forall p : positive, 0 <= Z.pos p
Zle_0_nat: forall n : nat, 0 <= Z.of_nat n
Zle_0_minus_le: forall n m : Z, 0 <= n - m -> m <= n
Zgt_succ_le: forall n m : Z, Z.succ m > n -> n <= m
Zgt_left: forall n m : Z, n > m -> 0 <= n + -1 + - m
Zgt_le_succ: forall n m : Z, m > n -> Z.succ n <= m
Zgt_0_le_0_pred: forall n : Z, n > 0 -> 0 <= Z.pred n
*)

SearchPattern (_ + _ <= _)%Z. (* works without %Z as we opened Z_scope *)
(*
Zplus_le_compat_r: forall n m p : Z, n <= m -> n + p <= m + p
Zplus_le_compat_l: forall n m p : Z, n <= m -> p + n <= p + m
*)

Open Scope nat_scope.
SearchPattern (_=_+_).

Open Scope Z_scope.
SearchPattern (_<=_).
SearchPattern (?X1 *_<= (* space here !!! *)?X1 *_).

Open Scope nat_scope.

Theorem lt_S: forall n p: nat, n < p -> n < S p.
Proof.
  intros n p H.
  unfold lt. (* delta reduction *)
  apply le_S.
  exact H.  (* the tactic exact takes care of delta reduction possible in H *)
Qed.

Definition opaque_f: nat->nat->nat.
  intros; assumption.
Qed. (* opaque definition, cannot unfold later *)

Lemma bad_proof_example_for_opaque: 
  forall x y:nat, opaque_f x y = y.
Proof.
  intros.
(*  unfold opaque_f. error *)
Abort.

Open Scope Z_scope.

Definition Zsquare_diff (x y:Z) := x*x - y*y.

Theorem unfold_example:
  forall x y:Z, x*x = y*y -> Zsquare_diff x y * Zsquare_diff (x+y)(x*y) = 0.
Proof.
  intros x y H.
  (* no point unfolding the second occurence *)
  unfold Zsquare_diff at 1. (* partial unfold *) 
  cut (x*x - y*y = 0).
  intro H'.
  rewrite -> H'.
  trivial.
(*Zplus_eq_compat *) (* forall n m p q : Z, n = m -> p = q -> n + p = m + q *)
  cut (y*y + -y*y = 0).
  intro.
  rewrite <- H0.
  cut (x*x + -y*y = x*x - y*y).
  intro.
  rewrite <- H1.
  apply Zplus_eq_compat with (n:=x*x)(m:=y*y)(p:=-y*y)(q:=-y*y).
  exact H.
  trivial.
(* Zplus_minus_eq *)
(* forall n m p : Z, n = m + p -> p = n - m *)
  apply Zplus_minus_eq.
  cut (x*x + -y*y = -y*y + x*x).
  intro.
  rewrite -> H1.
  cut (y*y + (- y*y + x*x) = (y*y + -y*y) + x*x).
  intro.
  rewrite -> H2.
  rewrite -> H0.
  trivial.
  apply Zplus_assoc.
  apply Zplus_comm.
  cut (0 = y*y + - y*y).
  intro. 
  rewrite <- H0.
  trivial.
  ring. (* jeeez, i wished i d used this one earlier *)
Qed.

Section ex_falso_quodlibet.
  Hypothesis ff: False.

  Lemma ex1: 220 = 284.
(* False_ind:  forall P : Prop, False -> P *)
  Proof.
    apply False_ind.
    exact ff.
  Qed.

  Lemma ex2: 220 = 284.
  Proof.
    elim ff.
  Qed.

End ex_falso_quodlibet.

Print ex2.

Theorem absurd : forall P Q: Prop, P->~P->Q.
Proof.
  intros P Q p H.
  elim H.
  exact p.
Qed.

Print absurd.

Theorem double_neg_i : forall P:Prop, P->~~P.
Proof.
  intro P.
  intro Hp.
  intro H.
  apply H.
  exact Hp.
Qed.

Theorem modus_ponens : forall P Q:Prop, P->(P->Q)->Q.
Proof.
  intros P Q Hp H.
  apply H; exact Hp.
Qed.

Theorem double_neg_i' : forall P:Prop, P->~~P.
Proof.
  intro P.
  Proof (modus_ponens (P:=P)(Q:=False)).

Lemma vim_confused: 0=0.
Proof.
  trivial.
Qed.

Theorem contrap: forall A B:Prop, (A->B)->~B->~A.
Proof.
  intros A B.
  unfold not.
  intros Hab Hnb Ha.
  apply Hnb. 
  apply Hab.
  exact Ha.
Qed.

Theorem imp_trans : forall P Q R: Prop, 
  (P->Q)->(Q->R)->(P->R).
Proof.
  intros P Q R Hpq Hqr Hp.
  apply Hqr.
  apply Hpq.
  exact Hp.
Qed.

Theorem contrap' : forall A B:Prop, (A->B)->~B->~A.
Proof.
  intros A B; unfold not.
  apply imp_trans.
Qed.

Theorem T1: ~False.
Proof.
  unfold not; intro; assumption.
Qed.

Lemma  L2: forall P:Prop, P->P.
Proof.
  intros P p;assumption.
Qed.

Theorem T2: ~False. (* proof did not use False_ind *)
Proof.
  unfold not.
  apply L2.
Qed.


Theorem T3: forall P:Prop, ~~~P->~P. (* cant prove ~~P->P, but this is not quite the same *)
(* this proof does not require False_ind *)
Proof.
  unfold not.
  intros P H Hp.
  apply H.
  intro H'.
  apply H'.
  exact Hp.
Qed.

Theorem T4: forall P Q R: Prop, (P->Q)->(P->~Q)->P->R.
Proof.
  intros P Q R H0 H1 Hp.
  apply False_ind.
  apply H1.
  exact Hp.
  apply H0; exact Hp.
Qed.

Theorem T5: (forall P Q, (P->Q)->(Q->P)) -> False.
Proof.
  intro H.
  apply H with (Q:=False->False).
  intros; assumption.
  intro;  assumption.
Qed.

Theorem T6: (forall P Q:Prop, (P->Q)->~P->~Q)-> False.
Proof.
  intro H.
  apply H with (P:=False)(Q:=False->False).
  intros; assumption.
  intro; assumption.
  intro; assumption.
Qed.

Theorem conj3' : forall P Q R:Prop, P->Q->R->P/\Q/\R.
Proof.
  repeat split; assumption.
Qed.

Theorem disj4_3' : forall P Q R S: Prop, R->P\/Q\/R\/S.
Proof.
 right; right; left; assumption. 
Qed.

Theorem and_comm: forall A B:Prop, A/\B -> B/\A.
Proof.
  intros A B H.
  elim H.
  split; assumption.
Qed.

Theorem or_comm: forall A B: Prop, A\/B -> B\/A.
Proof.
  intros A B H.
  elim H.
  right.
  exact H0.
  left.
  exact H0.
Qed.


Theorem T7: forall (A:Set)(a b c d:A), a=c \/ b=c \/ c=c \/ d=c.
Proof.
  intros A a b c d.
  right; right; left.
  reflexivity.
Qed.


Theorem T8: forall A B C:Prop, A/\(B/\C)->(A/\B)/\C.
Proof.
  intros A B C H.
  split.
  split.
  elim H.
  intro Ha.
  intro H'.
  exact Ha.
  elim H.
  intros Ha H0.
  elim H0.
  intros;assumption.
  elim H.
  intros Ha H0.
  elim H0.
  intros;assumption.
Qed.

Theorem T9: forall A B C D: Prop,
  (A->B)/\(C->D)/\A/\C->B/\D.
Proof.
  intros A B C D H.
  split.
  elim H.
  intro Hab.
  intro H'.
  elim H'.
  intro Hcd.
  intro H''.
  elim H''.
  intros Ha Hc.
  apply Hab; exact Ha.
  elim H.
  intros Hab H'.
  elim H'.
  intros Hcd H''.
  elim H''.
  intros Ha Hc.
  apply Hcd; exact Hc.
Qed.

Theorem T10: forall A:Prop, ~(A/\~A).
Proof.
  intro A.
  intro H.
  elim H.
  intros Ha Ha'.
  apply Ha'.
  exact Ha.
Qed.


Theorem T11: forall A B C:Prop, A\/(B\/C)->(A\/B)\/C.
Proof.
  intros A B C H.
  elim H.
  intro Ha.
  left;left;exact Ha.
  intro H'; elim H'.
  intro Hb.
  left;right;exact Hb.
  intro Hc.
  right; exact Hc.
Qed.


Theorem T12: forall A:Prop, ~~(A\/~A).
Proof.
  intro A.
  intro H.
  cut (~A).
  intro Ha.
  cut (~~A).
  intro Ha'.
  apply Ha'.
  exact Ha.
  intro.
  apply H.
  right.
  exact Ha.
  intro Ha.
  apply H.
  left.
  exact Ha.
Qed.

Theorem T13: forall A B: Prop, (A\/B)/\~A->B.
Proof.
  intros A B H.
  elim H.
  intros Hab Hna.
  elim Hab.
  intro Ha.
  apply False_ind.
  apply Hna.
  exact Ha.
  intro Hb; exact Hb.
Qed.


