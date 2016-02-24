(def bools [true true true false false])
(println (every? true? bools))  ; false

(println (some true? bools))    ; why do we have 'some' and not 'some?' is not clear
(println (some (fn[p] (= "rob" p)) ["kyle" "siva" "rob" "celeste"])) ; true

(println ((constantly 5) 45)) ; (constantly 5) is the same as (fn[&args] 5) it seems

(def f (complement every?))   ; returns function that takes same arguments, but with opposit boolean return value
(println (f true? bools))  ; true


(defn above-threshold? [threshold number]
  (> number threshold))

(println (filter (fn [x] (above-threshold? 5 x)) [1 2 3 4 5 6 7 8 9]))
; partial allows currying of function
(println (filter (partial above-threshold? 5) [1 2 3 4 5 6 7 8 9]))


