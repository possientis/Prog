(defn slow-calc [n m]
  (Thread/sleep 300)
  (* n m))

(def u [1 2 3])
(def v [3 4 5])

(println (map slow-calc u v))


(time (slow-calc 5 7))

(def fast-calc (memoize slow-calc))
(time (fast-calc 5 7))
(time (fast-calc 5 7))


; surely memoize cannot work for recursive functions :)
(defn fib [n]
  (cond (< n 1) 0
        (= n 1) 1
        :else (+ (fib (- n 1)) (fib (- n 2)))))

(println (map fib [0 1 2 3 4 5 6 7 8 9 10]))

(time (fib 37)) ; 1 second

(def fast-fib (memoize fib)) ; i don't think so

(time (fast-fib 37)) ; still 1 second


