open (* HolKernel *) arithmeticTheory;

val _ = new_theory "euclid";

val divides_def = Define `divides n m = ?k . k * n = m`;

set_fixity "divides" (Infix(NONASSOC, 450));

val prime_def = Define `prime p = p ≠ 1 ∧ !x. x divides p ⇒ (x = 1) ∨ (x = p)`;

g `!x. x divides 0`;

e (rw[divides_def]);

e (qexists_tac `0`);

e (rw []);

restart ();

e (rw[divides_def] >> qexists_tac `0` >> rw []);

restart ();

e (metis_tac [divides_def, MULT_CLAUSES]);

val DIVIDES_0 = top_thm();
drop ();

g `!x. 0 divides x = (x = 0)`;
e (metis_tac [divides_def, MULT_CLAUSES]);
val DIVIDES_ZERO = top_thm();
drop ();

g `!x. x divides 1 = (x = 1)`;
e (metis_tac [divides_def, MULT_CLAUSES, MULT_EQ_1]);
val DIVIDES_ONE = top_thm();
drop ();

g `!x. x divides x`;
e (metis_tac [divides_def, MULT_CLAUSES]);
val DIVIDES_REFL = top_thm();
drop ();

g `!a b c. a divides b ∧ b divides c ⇒ a divides c`;
e (metis_tac [divides_def, MULT_ASSOC]);
val DIVIDES_TRANS = top_thm();
drop ();

g `!d a b. d divides a ∧ d divides b ⇒ d divides (a+b)`;
e (metis_tac [divides_def, LEFT_ADD_DISTRIB]);

DIVIDES_0; DIVIDES_ZERO; DIVIDES_ONE; DIVIDES_REFL; DIVIDES_TRANS;






























