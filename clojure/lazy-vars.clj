(def ^:dynamic *factor* 10)

(defn multiply [x]
  (* x *factor*))

(println (map multiply [1 2 3 4 5])) ;; [10 20 30 40 50]

;; the effect of lazy execution on binding form:
;; when the actual result is needed (call to println)
;; we are outside the scope of the binding form

(println (binding [*factor* 20]
  (map multiply [1 2 3 4 5])))       ;; still [10 20 30 40 50] !!! 


(println (binding [*factor* 20]
  (doall (map multiply [1 2 3 4 5])))) ;; [20 40 60 80 100]


(println (binding [*factor* 20]
  (dorun (map multiply [1 2 3 4 5])))) ;; nil 
