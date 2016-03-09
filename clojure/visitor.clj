; visitor design pattern (double dispatch) revisited

; we want to maintain an AST (abstract syntax tree)

(def aNode {:type :assignment   :expr "assignment"})
(def vNode {:type :variable-ref :expr "variableref"})

(defmulti checkValidity :type)  ; :type is dispatch method
(defmethod checkValidity :assignment [node]
  (println "checking :assignment, expression is" (:expr node)))
(defmethod checkvalidity :variable-ref [node]
  (println "checking :variable-ref, expression is" (:expr node)))

(defmulti generateASM :type)
(defmethod generateASM :assignment [node]
  (println "gen ASM for :assignment, expr is" (:expr node)))
(defmethod generateASM :variable-ref [node]
  (println "gen ASM for :variable-ref, expr is" (:expr node)))
