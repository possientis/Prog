;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; map as the usual function on lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(println (+ 1 2 3 4))

; using map on 4 arguments function '+'
(println (map + '(1 2 3) '(1 2 3) '(1 2 3) '(1 2 3)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; map as a datatype, associative array, dictionary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def x {:a 1 :b 2 :c 3})
(def y {:a 1, :b 2, :c 3}) ; comma ',' optional 
(println x)
(println y)
(println (= x y)) ; true

(def z (hash-map :a 1 :b 2 :c 3))
(println z)
(println (= x z)) ; true

; a map is also a function excepting key as parameter
(println (list (x :a) (x :b) (x :c))) ; (1 2 3)
; a keyword is also a function expecting a sequence as parameter
(println (list (:a x) (:b y) (:c z))) ; (1 2 3)
