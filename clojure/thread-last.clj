(defn factorial [n]
  (apply * 
         (range 1
                (+ 1
                   n))))


(defn factorial->> [n]
  (->> n
       (+ 1)  ; thread-last macro places argument in last position
       (range 1)
       (apply *)))


(println (factorial 5))
(println (factorial->> 5))
