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

