(def x (range 1 101))

; this is the clojure syntactic construct to use tail-recursion
; this implementation can withstand a very large list
(defn total1 [numbers]
  (loop [l numbers sum 0]
    (if (empty? l)
      sum
      (recur (rest l) (+ (first l) sum))))) ; fold-left

(println (total1 x)) 


; not tail recursive, stack will soon overflow
(defn total2 [numbers]
  (if (empty? numbers)
    0
    (+ (first numbers) (total2 (rest numbers))))) ; fold-right

(println (total2 x))

; tail recursive, but no tail-recursive optimization in Clojure
; stack will soon overflow
(defn total3 [numbers]
  (letfn [(my-loop [l sum]
            (if (empty? l)
              sum
              (my-loop (rest l) (+ (first l) sum))))] ; fold-left
    (my-loop numbers 0)))


(println (total3 x))

; same code, but tail recursion optimization explicitly enforced
; by the use of the 'recur' keyword. Can withstand a very large list.
(defn total4 [numbers]
  (letfn [(my-loop [l sum]
            (if (empty? l)
              sum
              (recur (rest l) (+ (first l) sum))))] ; fold-left
    (my-loop numbers 0)))


(println (total4 x))


(println (conj '(1 2 3) 4))
(println (cons 4 '(1 2 3)))
(println \a) ; char literal









