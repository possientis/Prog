(defmacro randomly [& exprs]
  (let [len (count exprs)
        index (rand-int len)
        conditions (map #(list '= index %) (range len))]
    `(cond ~@(interleave conditions exprs))))

(println (macroexpand-1 '(randomly (println "amit") (println "deepthi") (println "adi"))))

(randomly (println "amit") (println "deepthi") (println "adi"))
(randomly (println "amit") (println "deepthi") (println "adi"))
(randomly (println "amit") (println "deepthi") (println "adi"))
(randomly (println "amit") (println "deepthi") (println "adi"))
(randomly (println "amit") (println "deepthi") (println "adi"))
(randomly (println "amit") (println "deepthi") (println "adi"))
(randomly (println "amit") (println "deepthi") (println "adi"))


(defn f []
  (randomly (println "amit") (println "deepthi") (println "adi")))
(println "from function:")
(f)
(f)
(f)
(f)
(f)
(f)
(f)
(f)



(def g (fn [] (randomly (println "amit") (println "deepthi") (println "adi"))))

(println "from other function")
(g)
(g)
(g)
(g)
(g)
(g)
(g)



