(def c (cycle [1 2 3 4]))

(println (take 15 c))
(println (first c))
(println (take 14 (rest c)))

(def ones 
  (lazy-seq
    (cons 1 ones)))

(println (take 10 ones))

(def integers
  (lazy-seq
    (cons 1 (map + integers ones))))

(println (take 10 integers))

(defn positive-numbers
  ([] (positive-numbers 1))
  ([n](lazy-seq (cons n (positive-numbers (inc n))))))  ; overloading

(println (take 10 (positive-numbers)))

; another fibonacci
(defn sum-last-2
  ([] (sum-last-2 0 1))
  ([n m] (cons n (lazy-seq (sum-last-2 m (+ n m))))))

(println (take 15 (sum-last-2))) 

(defn sieve [s]
  (let [x (first s)]
    (cons x (lazy-seq (sieve (filter #(not= 0 (mod % x)) (rest s)))))))

(println (take 10 (iterate inc 2)))

(def primes (sieve (iterate inc 2)))

(println (take 138 primes))

