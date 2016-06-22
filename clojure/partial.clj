(defn sum [x y z]
  (+ x y z))

(def f (partial sum 5 7)) ; currying

(println (f 8)) ; 20
