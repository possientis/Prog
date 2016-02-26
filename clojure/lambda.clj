; creating anonymous function, aka lambda expressions, which are
; sometimes clojures, use 'fn' and '#' macro

(def func1 (fn [x y] (+ x y)))
(def func2 #(+ % 4))
(def func3 #(+ %1 %2))  ; starts from %1...

(println (func1 3 4))
(println (func2 3))
(println (func3 3 4))


; the macro # cannot be nested (or re-entrant?)
;(def func4 #(+ % (#(+ 1 %) 3))) ; won't comply
