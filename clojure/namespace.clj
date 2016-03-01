; defining a namespace
(ns org.currylogic.damages.calculators)

(defn highest-expense-during [start-date end-date]
  ;; (logic to find the answer)
  )

; all namespaces which are currently loaded
(println (all-ns))

; #<Namespace clojure.core> #<Namespace clojure.uuid> 
; #<Namespace clojure.java.io> #<Namespace clojure.main> 
; #<Namespace user> #<Namespace org.currylogic.damages.calculators> 
; #<Namespace clojure.core.protocols> #<Namespace clojure.instant> 
; #<Namespace clojure.string>)

(println (find-ns 'non.existant.name.space)) ; nil
(println (find-ns 'clojure.core)) ; #<Namespace clojure.core>
(println (find-ns 'clojure.uuid)) ; #<Namespace clojure.uuid>
(println (find-ns 'clojure.java.io)) ; #<Namespace clojure.java.io>
(println (find-ns 'clojure.main)) ; #<Namespace clojure.main>
(println (find-ns 'org.currylogic.damages.calculators)) 



