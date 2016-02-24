; foldleft but not as flexible since binary
; operator is constrained to have both arguments
; same type
(println (reduce * [1 2 3 4 5]))
(println (reduce + '(1 2 3 4 5)))

; syntactic sugar for
(def x
  (loop [acc 1 v [1 2 3 4 5]]
    (if (empty? v)
      acc
      (recur (* acc (first v)) (rest v)))))

(println x)


