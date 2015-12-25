(def x
  (let [my-vector [1 2 3 4]
        my-map {:fred "ethel" :ricky "lucy"}
        my-list (list 4 3 2 1)]
    [(first my-vector)
     (rest my-vector)
     (keys my-map)
     (vals my-map)
     (first my-list)
     (rest my-list)]))

(println x)
