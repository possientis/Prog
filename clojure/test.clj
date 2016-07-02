(def x (Exception. "Illegal stuff"))
(def y {:key1 "hello" :key2 "world"})

(println (class x)) ; java.lang.Exception
(println (class y)) ; clojure.lang.PersistentHashMap


