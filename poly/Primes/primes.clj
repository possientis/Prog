(ns primes (:gen-class))

(defn sieve [s]
  (let [x (first s)]
    (cons x (lazy-seq (sieve (filter #(not= 0 (mod % x)) (rest s)))))))

(defn -main [arg]
  (def numPrimes (read-string arg))
  (def from2 (iterate inc 2))
  (def primes (sieve from2))
  (println (take numPrimes primes)))


;(-main "138")
