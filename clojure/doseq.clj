(def v '("abc" "def" "ghi"))
(def w ["abc" "def" "ghi"])
(println (list? v))
(println (vector? w))

; foreach construct
(println)
(doseq [s v] (println s)) ; foreach
(println)
(doseq [s w] (println s)) ; foreach
(println)

; syntactic sugar for:
(loop [l v]
  (if (not (empty? l))
    (do (println (first l))
        (recur (rest l)))))

(println)

(println (first v))
(println (rest v))
(println (rest (rest v)))
(println (rest (rest (rest v))))
(def x (rest (rest (rest v))))
(def y (rest (rest (rest w))))
(println (= '() x)) ; true
(println (nil? x))  ; false
(println (= '() y)) ; true  
(println (nil? y))  ; false
(println (empty? x))
(println (empty? y))

