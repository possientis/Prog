(def x
  (let [my-vector [1 2 3 4]
        my-map {:fred "ethel"}
        my-list (list 4 3 2 1)]
    (list
      (conj my-vector 5)
      (assoc my-map :ricky "lucy")
      (conj my-list 5)
      ; the originals are intact
      my-vector
      my-map
      my-list)))

(println x)
