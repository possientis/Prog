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

val ONE_def = Define `ONE(out:num->bool) = !t. out t = T`;

val NOT_def = Define `NOT(inp, out:num->bool) = !t. out t = ¬(inp t)`;

val MUX_def = Define `MUX(sw,in1,in2,out:num->bool) = 
  !t. out t = if sw t then in1 t else in2 t`;

val REG_def = Define `REG(inp,out:num->bool) = 
  !t. out t = if t = 0 then F else inp (t-1)`;

val PARITY_IMP_def = Define `PARITY_IMP(inp,out) =
  ∃ l1 l2 l3 l4 l5.
    NOT (l2,l1) ∧ MUX (inp,l1,l2,l3)    ∧ REG(out,l2) ∧
    ONE l4      ∧ REG(l4,l5)            ∧ MUX(l5,l3,l4,out)`;

val PARITY_LEMMA = store_thm
    ( "PARITY_LEMMA"
    , ``!inp out.
        PARITY_IMP(inp,out) ⇒ 
        (out 0 = T) ∧ 
        !t. out(SUC t) = if inp(SUC t) then ¬(out t) else out t``
    ,   PURE_REWRITE_TAC [PARITY_IMP_def, ONE_def, NOT_def, MUX_def, REG_def]
        >> rpt strip_tac
        >> metis_tac []
        >> qpat_x_assum `!t. out t = X t` 
           (fn th => REWRITE_TAC [SPEC ``SUC t`` th])
        >> rw []
    );


val PARITY_CORRECT = prove
    ( ``!inp out. PARITY_IMP(inp,out) ⇒ (!t. out t = PARITY t inp)``
    ,       rpt strip_tac 
        >>  match_mp_tac UNIQUENESS_LEMMA
        >> irule PARITY_LEMMA
        >> rw []
    );

val _ = export_theory();
