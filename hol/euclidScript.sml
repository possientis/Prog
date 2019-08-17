open (* HolKernel *) arithmeticTheory;

(* val _ = new_theory "euclid"; *)

val divides_def = Define `divides n m = ?k . k * n = m`;

set_fixity "divides" (Infix(NONASSOC, 450));

val prime_def = Define `prime p = p ≠ 1 ∧ !x. x divides p ⇒ (x = 1) ∨ (x = p)`;

(* Lemma *)
g `!x. x divides 0`;
(* Proof *)
e (rw[divides_def]);
e (qexists_tac `0`);
e (rw []);

(* Another proof *)
restart ();
e (rw[divides_def] >> qexists_tac `0` >> rw []);

(* Another proof *)
restart ();
e (metis_tac [divides_def, MULT_CLAUSES]);

(* bind lemma to name *)
val DIVIDES_0 = top_thm();

(* remove lemma from goal stack *)
drop ();

(* Lemma *)
`!x. 0 divides x = (x = 0)`
(* Proof *)
rw[divides_def]
(* Qed *)
val DIVIDES_ZERO = top_thm();
drop ();

(*
(* automated proof *)
restart ();
e (metis_tac [divides_def, MULT_CLAUSES]);
*)

(* Lemma *)
`!x. x divides 1 = (x = 1)`
(* Proof *)
rw [divides_def]
(* Qed *)
val DIVIDES_ONE = top_thm();
drop ();

(*
(* automated proof *)
e (metis_tac [divides_def, MULT_CLAUSES, MULT_EQ_1]);
*)

(* Lemma *)
`!x. x divides x`
(* Proof *)
rw [divides_def]
qexists_tac `1`
rw [MULT_EQ_1]
(* Qed *)
val DIVIDES_REFL = top_thm();
drop ();

(*
(* automated proof *)
e (metis_tac [divides_def, MULT_CLAUSES]);
*)

(* Lemma *)
`!a b c. a divides b ∧ b divides c ⇒ a divides c`
(* Proof *)
rw [divides_def]
qexists_tac `k * k'`
rw [MULT_ASSOC]
(* Qed *)
val DIVIDES_TRANS = top_thm();
drop ();

(*
(* automated proof *)
e (metis_tac [divides_def, MULT_ASSOC]);
*)

(* Lemma *)
`!d a b. d divides a ∧ d divides b ⇒ d divides (a+b)`
(* Proof *)
rw [divides_def]
qexists_tac `k + k'`
rw [LEFT_ADD_DISTRIB]
(* Qed *)
val DIVIDES_ADD = top_thm();
drop ();


(* Lemma *)
`!d a b. d divides a ∧ d divides b ⇒ d divides (a-b)`
(* Proof *)
rw [divides_def]
qexists_tac `k - k'`
rw [LEFT_SUB_DISTRIB]
(* Qed *)
val DIVIDES_SUB = top_thm();
drop ();

(* proofs appear to be stuck in infinite loop
g `!d a b. d divides a ∧ d divides b ⇒ d divides (a+b)`;
e (metis_tac [divides_def, LEFT_ADD_DISTRIB]);


g `!d a b. d divides a ∧ d divides b ⇒ d divides (a-b)`;
e (metis_tac [divides_def, LEFT_SUB_DISTRIB]);
*)

DIVIDES_0; 
DIVIDES_ZERO; 
DIVIDES_ONE; 
DIVIDES_REFL; 
DIVIDES_TRANS;
DIVIDES_ADD;
DIVIDES_SUB;

