(println "Hello world")

(defn factorial [n]
  (if (< n 1) 1
    (* n (factorial (- n 1)))))

(println (factorial 5))
