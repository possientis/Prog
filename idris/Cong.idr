same_cons : {xs : List a } -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons p = cong p

eq_trans : x = y -> y = z -> x = z
eq_trans Refl q = q

f1 : List a -> a -> a
f1 xs x = x :: xs

same_lists : {xs : List a} -> {ys : List a} -> {x:a} -> {y:a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists {xs} {ys} p q = let g1 = f1 xs in eq_trans (cong {g1} p) ?e2


