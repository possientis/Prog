same_cons : {xs : List a } -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons p = cong p

eq_trans : x = y -> y = z -> x = z
eq_trans Refl q = q

-- Cannot get this to work
same_lists : {xs : List a} -> {ys : List a} -> {x:a} -> {y:a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists {xs} {ys} p q = eq_trans (cong p) (cong q)


