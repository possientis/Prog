(defn my-zipmap [keys vals]
  (loop [my-map {}
         my-keys (seq keys)
         my-vals (seq vals)]
    (if (and my-keys my-vals)
      (recur (assoc my-map (first my-keys) (first my-vals))
             (next my-keys)
             (next my-vals))
      my-map)))

(println (my-zipmap [:a :b :c] [1 2 3]))
