lemma L1 (a b : Prop) (Ha : a) (Hb : b) : a := by apply Ha

set_option pp.beta true -- aggressive beta reduction
set_option trace.simplify.rewrite true

