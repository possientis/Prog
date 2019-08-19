open HolKernel arithmeticTheory;

val _ = new_theory "euclid";

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
g `!x. 0 divides x = (x = 0)`;
(* Proof *)
e (rw[divides_def]);
(* Qed *)
val DIVIDES_ZERO = top_thm();
drop ();

(*
(* automated proof *)
restart ();
e (metis_tac [divides_def, MULT_CLAUSES]);
*)

(* Lemma *)
g `!x. x divides 1 = (x = 1)`;
(* Proof *)
e (rw [divides_def]);
(* Qed *)
val DIVIDES_ONE = top_thm();
drop ();

(*
(* automated proof *)
e (metis_tac [divides_def, MULT_CLAUSES, MULT_EQ_1]);
*)

(* Lemma *)
g `!x. x divides x`;
(* Proof *)
e (rw [divides_def]);
e (qexists_tac `1`);
e (rw [MULT_EQ_1]);
(* Qed *)
val DIVIDES_REFL = top_thm();
drop ();

(*
(* automated proof *)
e (metis_tac [divides_def, MULT_CLAUSES]);
*)

(* Lemma *)
g `!a b c. a divides b ∧ b divides c ⇒ a divides c`;
(* Proof *)
e (rw [divides_def]);
e (qexists_tac `k * k'`);
e (rw [MULT_ASSOC]);
(* Qed *)
val DIVIDES_TRANS = top_thm();
drop ();

(*
(* automated proof *)
e (metis_tac [divides_def, MULT_ASSOC]);
*)

(* Lemma *)
g `!d a b. d divides a ∧ d divides b ⇒ d divides (a+b)`;
(* Proof *)
e (rw [divides_def]);
e (qexists_tac `k + k'`);
e (rw [LEFT_ADD_DISTRIB]);
(* Qed *)
val DIVIDES_ADD = top_thm();
drop ();


(* Lemma *)
g `!d a b. d divides a ∧ d divides b ⇒ d divides (a-b)`;
(* Proof *)
e (rw [divides_def]);
e (qexists_tac `k - k'`);
e (rw [LEFT_SUB_DISTRIB]);
(* Qed *)
val DIVIDES_SUB = top_thm();
drop ();

(* proofs appear to be stuck in infinite loop
g `!d a b. d divides a ∧ d divides b ⇒ d divides (a+b)`;
e (metis_tac [divides_def, LEFT_ADD_DISTRIB]);


g `!d a b. d divides a ∧ d divides b ⇒ d divides (a-b)`;
e (metis_tac [divides_def, LEFT_SUB_DISTRIB]);
*)

g `!d a b. d divides a /\ d divides (a + b) ==> d divides b`;
e (rw [divides_def]);
e (qexists_tac `k' - k`); 
e (rw [ADD_SYM]);
val DIVIDES_ADDL = top_thm();
drop ();

g `!d a x. d divides a ⇒ d divides (x * a)`;
e (rw [divides_def]);
e (qexists_tac `k * x`);
e (rw [MULT_ASSOC]);
val DIVIDES_LMUL = top_thm();
drop ();


g `!d a x. d divides a ⇒ d divides (a * x)`;
e (rw [divides_def]);
e (qexists_tac `k * x`);
e (rw [MULT_ASSOC]);
val DIVIDES_RMUL = top_thm();
drop ();

g `!m n. m divides n ⇒ m ≤ n ∨ (n = 0)`;
e (rw [divides_def]);

DB.match ["arithmetic"] ``m ≤ x * m``;

e (rw [LE_MULT_CANCEL_LBARE]);
val DIVIDES_LE = top_thm();
drop ();


val DIVIDES_LE2 = store_thm(
    "DIVIDES_LE2",
    ``!m n. m divides n ⇒ m ≤ n ∨ (n = 0)``,
    rw [divides_def] >> rw []);

DIVIDES_0; 
DIVIDES_ZERO; 
DIVIDES_ONE; 
DIVIDES_REFL; 
DIVIDES_TRANS;
DIVIDES_ADD;
DIVIDES_SUB;
DIVIDES_ADDL;
DIVIDES_LMUL;
DIVIDES_RMUL;
DIVIDES_LE;
DIVIDES_LE2;


