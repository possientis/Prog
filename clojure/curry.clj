; creates a curried version of the given function
(defn curried-fn [func args-len]
  (fn [& args]
    (let [remaining (- args-len (count args))]
      (if (< remaining 0) (throw (Exception. "illegal number of arguments"))
        (if (zero? remaining)
          (apply func args)
          (curried-fn (apply partial (conj args func)) remaining))))))


(defn sum [x y z t]
  (+ x y z t))

(def curried-sum (curried-fn sum 4))


(def sum1 (curried-sum 4))
(println (sum1 5 6 7))  ; 22

(def sum2 (sum1 5))
(println (sum2 6 7))    ; 22

(def sum3 (sum2 6))
(println (sum3 7))      ; 22

(def sum4 (sum3 7))
(println sum4)          ; 22

(defmacro defcurried [fname args & body]
  `(let [fun# (fn ~args (do ~@body))]
     (def ~fname (curried-fn fun# ~(count args)))))

(defcurried new-sum [x y z t] (+ x y z t))

(println (str (macroexpand-1 '(defcurried new-sum [x y z t] (+ x y z t)))))
(comment
(let [fun__13__auto__ (fn [x y z t] (do (+ x y z t)))] 
  (def new-sum (curried-fn fun__13__auto__ 4)))
)

(def sum5 (new-sum 4))
(println (sum5 5 6 7))  ; 22

(def sum6 (sum5 5))
(println (sum6 6 7))    ; 22

(def sum7 (sum6 6))
(println (sum7 7))      ; 22






