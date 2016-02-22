(defn item-total [price quantity]
  {:pre [(> price 0) (> quantity 0)]
   :post [(> % 0)]}
  (* price quantity))


(println (item-total 120 5))  ; valid input
;(println (item-total 0 5))

; business logic
(defn basic-item-total [price quantity]
  (* price quantity))

; business logic decoupled from pre and post conditions checks
(defn with-line-item-conditions [f price quantity]
  {:pre [(> price 0) (> quantity 0)]
   :post [(> % 1)]}
;  (apply f [price quantity]))
; apply is not needed here as we are not given a list
; of arguments, but rather the arguments themselves
  (f price quantity))


(println (with-line-item-conditions basic-item-total 20 1))
