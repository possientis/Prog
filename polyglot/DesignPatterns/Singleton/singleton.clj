; Singleton design pattern
(ns singleton (:gen-class))

(def SingleObject   ; 
  (letfn
    ; instance interface
    [(instance[m]
        (cond (= m :showMessage) (showMessage)
               :else (println "SingleObject: unknown instance operation error")))
     (showMessage []
       (println "The single object is alive and well"))
    ; static interface
     (static [m]
       (cond (= :getInstance) (getInstance)
             :else (println "SingleObject: unknown static operation error")))
     (getInstance []
       instance)]
    ; returning static interface
    static))

(defn -main []
(def object1 (SingleObject :getInstance))
(object1 :showMessage)
(def object2 (SingleObject :getInstance))
(if (= object1 object2) (println "The two objects are the same")))

;(-main)






