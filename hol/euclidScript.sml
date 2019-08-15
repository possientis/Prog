open HolKernel arithmeticTheory;

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

DIVIDES_0; DIVIDES_ZERO;

