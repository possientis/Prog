(defn fib-from [term-1 term-2]
  (let [term-3 (+ term-1 term-2)]
    (lazy-seq (cons term-3 (fib-from term-2 term-3)))))

; language comment: possible to use '(0 1) instead of [0 1]
(def fib (concat [0 1] (fib-from 0 1)))

(println (take 15 fib))
