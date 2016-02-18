(println (vector? [1,2,3])) ; true
(println (list? [1,2,3]))   ; false
(println (list? '(1,2,3)))  ; true
(println (vector? (rest [1,2,3])))  ; false
(println (list? (rest [1,2,3])))    ; false
(println (rest [1,2,3]))    ; ( 2 3) but seemingly not a list
(println (seq? [1,2,3]))    ; false
(println (seq? '(1,2,3)))   ; true
(println (seq? (rest [1,2,3]))) ; not a list but a seq

(println (= [1,2,3] [1 2 3])) ; true

