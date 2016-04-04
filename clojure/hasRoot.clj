; checking whether a variable has a binding
(def v (def x))

(println v)         ; #'user/x
(println (var v))   ; #'user/v
(println (eval v))  ; #'user/x

(println (.hasRoot v))        ; false
(println (.hasRoot (var x)))  ; false 

(def w (def y 10))

(println (.hasRoot w))        ; true
(println (.hasRoot (var y)))  ; true


(println (macroexpand '(when-not x y)))

(println (macroexpand-1 '(defonce name expr)))

(println (macroexpand-1 '(and a b c d e)))
(println (macroexpand-1 '(and)))
(println (macroexpand-1 '(and 'anything)))

(println (macroexpand-1 '(time expr))) 

(prn "hello")

(time (prn "hihi"))
(time (do
(println (. System (nanoTime)))
(println (. System (nanoTime)))))


