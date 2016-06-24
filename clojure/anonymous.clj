(defn add-pair [x y] (+ x y))

; the anonymous function reader macro: -> function literal
(def inc-by-3 #(add-pair 3 %1))

(println (inc-by-3 11)) ; 14

(def also-inc-by-3 (partial add-pair 3))

(println (also-inc-by-3 11))  ; 14

(def half-of #(/ %1 2))

(println (half-of 7)) ; 7/2

(defn add-numbers [& numbers]
  (apply + numbers))

(println (add-numbers 1 2 3 4 5)) ; 15

(def add-5-to-remaining #(apply add-numbers 2 3 %&))


(println (add-5-to-remaining 1 2 3 4))  ; 15




