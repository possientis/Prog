; def creates global binding
(defn foo[]
  (def x :globalvalue))

(foo)
(println x) ; :globalvalue


(def ^:dynamic unbound1)      ; this is possible
(println unbound1)            ; #<Unbound Unbound: #'user/unbound1>
(def ^:dynamic unbound2)

(binding [unbound1 :value1
          unbound2 :value2]
  (println "unbound1 = " unbound1)
  (println "unbound2 = " unbound2)) ; binding only persists in body of 'binding'


(println "unbound1 = " unbound1)    ; binding is gone




