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
(println (find-ns 'clojure.core))     ; #<Namespace clojure.core>
(println (find-ns 'clojure.uuid))     ; #<Namespace clojure.uuid>
(println (find-ns 'clojure.java.io))  ; #<Namespace clojure.java.io>
(println (find-ns 'clojure.main))     ; #<Namespace clojure.main>
(println (find-ns 'user))             ; #<Namespace user>
(println (find-ns 'org.currylogic.damages.calculators)) 
(println (find-ns 'clojure.core.protocols))
(println (find-ns 'clojure.instant))
(println (find-ns 'clojure.string))


(println (ns-interns 'user))          ; returns a map with every binding
(def x 42)
(println (ns-interns 'user))          ; still {} despite 'def'
(println (ns-interns 'org.currylogic.damages.calculators)) 
; {highest-expense-during #'org.currylogic.damages.calculators/highest-expense-during, 
; x #'org.currylogic.damages.calculators/x}
(def dict (ns-interns 'org.currylogic.damages.calculators))
(def y (dict 'x))
(println y)  ; #'org.currylogic.damages.calculators/x

(println (ns-interns 'clojure.string))
(println (ns-interns 'clojure.core))
(println "----------------------------------------------------------------------------------------")
(println (ns-interns 'clojure.main))
(println "----------------------------------------------------------------------------------------")
(println (ns-publics 'clojure.main))  ; same but only public names
(println "----------------------------------------------------------------------------------------")
(println (ns-resolve 'org.currylogic.damages.calculators 'x)) ; #'org.currylogic.damages.calculators/x
(println (ns-resolve 'org.currylogic.damages.calculators 'unfound)) ; nil
(println (resolve 'x)) ; same as ns-resolve but uses current namespace

(ns-unmap 'org.currylogic.damages.calculators 'x) ; removes binding
(println (resolve 'x)) ; now nil

;; be very careful see below
(remove-ns 'org.currylogic.damages.calculators)   ; removes namespace altogether

(println (all-ns)) ; 'org.currylogic.damages.calculators no longer there

(def x 45)  ; should now hit 'user namespace
(println (ns-interns 'user)) ; {} !!!!!!! I am wrong          
(println x)                  ; #<Unbound Unbound: #'org.currylogic.damages.calculators/x>

