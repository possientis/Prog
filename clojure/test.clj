(def f
  (fn [x] 
    (defn g [x] (* 2 x))
    (* (g x) (g x))))


(def g 
  (let [a 3]
    (defn h [x] (* x x))
    (* a a)))



(println f)
;(println a)
(println g)
(println h)
