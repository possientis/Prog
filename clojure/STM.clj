; STM: software transactional memory

(def total-expenditure (ref 0))
;; using this function will throw a "No transaction running"
;; IllegalStateException exception
(defn add-amount-1 [amount]
  (ref-set total-expenditure (+ amount @total-expenditure)))
;; The following will work fine because it will do the update inside a
;; transaction
(defn add-amount-2 [amount]
  (dosync (ref-set total-expenditure (+ amount @total-expenditure))))


(println @total-expenditure)
(add-amount-2 100)
(println @total-expenditure)
(add-amount-2 300)
(println @total-expenditure)
