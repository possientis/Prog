(defn argcount
  ([] 0)
  ([x] 1)
  ([x y] 2)
  ([x y & z] (+ (argcount x y) (count z))))

(println (argcount))
(println (argcount :ignored))
(println (argcount :ignored :ignored))
(println (argcount 1 2 3 4 5))


