open parityTheory;

open HolKernel boolLib Parse bossLib

val _ = new_theory "parity";

val PARITY_def = Define `
    (PARITY 0 f = T) ∧
    (PARITY (SUC n) f = if f(SUC n) then ~PARITY n f else PARITY n f)`;

val UNIQUENESS_LEMMA = store_thm
    ( "UNIQUENESS_LEMMA"
    , ``!inp out.
        (out 0 = T) ∧
        (!t. out (SUC t) = (if inp (SUC t) then ¬(out t) else out t)) ⇒
        (!t. out t = PARITY t inp)``
    , (rpt gen_tac) >> strip_tac >> Induct >> rw [PARITY_def]
    );


val _ = export_theory();
