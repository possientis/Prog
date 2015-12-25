(def v [1 2 3])
(def attributed-v (with-meta v {:source :trusted})) ; = v , with meta info
(println (:source (meta attributed-v))) ; meta info can be queried
(println (= v attributed-v))  ; no change in equality semantics, still true
