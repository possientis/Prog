; function
(defn my-func [x] 3)
(defn my-documented-func "Returns the constant 3" [x] 3)

(println (my-func 7)) ; 3
(println (my-documented-func 8)) ; 3

