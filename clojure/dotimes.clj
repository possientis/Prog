(dotimes [i 5]
  (println i))  ; for(i = 0; i < 5; ++i)

; syntactic sugar for
(println)
(loop [i 0]
  (if (< i 5)
    (do (println i)
        (recur (+ i 1)))))
