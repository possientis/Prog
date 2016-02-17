(defn prime? [x]
  (let [divisors (range 2 (inc (int (Math/sqrt x))))
        remainders (map #(rem x %) divisors)]
    (not (some zero? remainders))))

(defn primes-less-than [n]
  (for [x (range 2 (inc n)) :when (prime? x)]
    x))

; syntactic sugar for 
(defn primes-less-than2 [n]
  (for [x (filter prime? (range 2 (inc n)))]
    x))

(defn pairs-for-primes [n]
  (let [z (range 2 (inc n))]
    (for [x z y z :when (prime? (+ x y))]
      (list x y))))


(println (pairs-for-primes 5))
