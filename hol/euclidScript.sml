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
e (
    rw[divides_def] >> 
    qexists_tac `0` >> 
    rw []
);

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

(* automated proof *)
restart ();
e (metis_tac [divides_def, MULT_CLAUSES]);

(* Qed *)
val DIVIDES_ZERO = top_thm();
drop ();


(* Lemma *)
g `!x. x divides 1 = (x = 1)`;
(* Proof *)
e (rw [divides_def]);

(* automated proof *)
restart();
e (metis_tac [divides_def, MULT_CLAUSES, MULT_EQ_1]);

(* Qed *)
val DIVIDES_ONE = top_thm();
drop ();

(* Lemma *)
g `!x. x divides x`;
(* Proof *)
e (rw [divides_def]);
e (qexists_tac `1`);
e (rw [MULT_EQ_1]);

(* automated proof *)
restart();
e (metis_tac [divides_def, MULT_CLAUSES]);


(* Qed *)
val DIVIDES_REFL = top_thm();
drop ();

(* Lemma *)
g `!a b c. a divides b ∧ b divides c ⇒ a divides c`;
(* Proof *)
e (rw [divides_def]);
e (qexists_tac `k * k'`);
e (rw [MULT_ASSOC]);

(* automated proof *)
restart();
e (metis_tac [divides_def, MULT_ASSOC]);

(* Qed *)
val DIVIDES_TRANS = top_thm();
drop ();

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


g `!m n. 0 < m /\ m ≤ n ⇒ m divides (FACT n)`;

e (
    `!m p. 0 < m ⇒ m divides FACT (m + p)` 
    suffices_by metis_tac[LESS_EQ_EXISTS]
);

e ( Induct_on `p`);

e (rw[]);

e (Cases_on `m`);

(*
e (metis_tac [DECIDE ``!x.~(x < x)``]);
*)

e (fs []);

e (rw [FACT]);

e (rw [DIVIDES_LMUL, DIVIDES_REFL]);

e (rw [ADD_CLAUSES]);

e (rw [FACT]);

e (rw [DIVIDES_RMUL]);

restart ();
e (
    `!m p. 0 < m ⇒ m divides FACT (m + p)` 
    suffices_by metis_tac[LESS_EQ_EXISTS]   >>
    Induct_on `p` >| [
        rw [] >> Cases_on `m` >| [
            fs [],
            rw [FACT] >> rw [DIVIDES_LMUL, DIVIDES_REFL]
        ],
        rw [ADD_CLAUSES] >> rw [FACT] >> rw [DIVIDES_RMUL]
    ]
);

restart ();
e (
    `!m p. 0 < m ⇒ m divides FACT (m + p)` 
    suffices_by metis_tac[LESS_EQ_EXISTS]   >>
    Induct_on `p` >| [
        Cases_on `m` >| [
            fs [],
            rw [FACT] >> rw [DIVIDES_LMUL, DIVIDES_REFL]
        ],
        rw [ADD_CLAUSES] >> rw [FACT] >> rw [DIVIDES_RMUL]
    ]
);

restart ();
e (
    `!m p. 0 < m ⇒ m divides FACT (m + p)` 
    suffices_by metis_tac[LESS_EQ_EXISTS]   >>
    Induct_on `p` >| [
        Cases_on `m` >| [
            fs [],
            rw [FACT, DIVIDES_LMUL, DIVIDES_REFL]
        ],
        rw [ADD_CLAUSES, FACT, DIVIDES_RMUL]
    ]
);


restart ();
e (
    `!m p. 0 < m ⇒ m divides FACT (m + p)` 
    suffices_by metis_tac[LESS_EQ_EXISTS]   >>
    Induct_on `p`                           >> 
    rw [ADD_CLAUSES, FACT, DIVIDES_RMUL]    >>
    (* base case only remains *)
    Cases_on `m` >| [
        fs [],
        rw [FACT, DIVIDES_LMUL, DIVIDES_REFL]
    ]
);

restart ();
e (
    `!m p. 0 < m ⇒ m divides FACT (m + p)` 
    suffices_by metis_tac[LESS_EQ_EXISTS]   >>
    Induct_on `p`                           >> 
    rw [ADD_CLAUSES, FACT, DIVIDES_RMUL]    >>
    (* base case only remains *)
    Cases_on `m`                            >>
    fs [FACT, DIVIDES_LMUL, DIVIDES_REFL]
);


restart ();
e (Induct_on `n - m`);

b();

e (Induct_on `n - m` >> rw[]);
e (`m = n` by rw[]);
e (rw[]);
e (`?k. m = SUC k` by (Cases_on `m` >> fs[]));
e (fs [FACT, DIVIDES_LMUL, DIVIDES_REFL]);

e (`0 < n` by rw[] >> `?k. n = SUC k` by (Cases_on `n` >> fs[]));
e (rw[FACT,DIVIDES_RMUL]);
val DIVIDES_FACT = top_thm();
drop();

g `~prime 0`;
e (rw[prime_def]);
e (rw[DIVIDES_0]);
restart ();
e (rw[prime_def,DIVIDES_0]);
val NOT_PRIME_0 = top_thm();
drop();

g `~prime 1`;
e (rw[prime_def]);
val NOT_PRIME_1 = top_thm();
drop();

g `prime 2`;
e (rw[prime_def]);
(* How am I supposed to come up with this ? *)
e (metis_tac [DIVIDES_LE, DIVIDES_ZERO, DECIDE ``2<>0``,
    DECIDE ``x ≤ 2 ⇔ (x=0) ∨ (x=1) ∨ (x=2)``]);
val PRIME_2 = top_thm();
drop();


g `!p. prime p ⇒ 0 < p`
e (Cases);
e (rw[NOT_PRIME_0]);
restart();
e(Cases >> rw[NOT_PRIME_0]);
val PRIME_POS = top_thm();
drop();

LESS_EQ_EXISTS;
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
DIVIDES_FACT;
NOT_PRIME_0;
PRIME_2;
PRIME_POS;


