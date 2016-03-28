; promise, very useful for dataflow
(def p (promise)) ; no argument

(defn some-task[]
  (println "task starting")
  (Thread/sleep 1000)
  (deliver p 100) ; binding promise from another thread
  (println "task complete"))

(def x (future (some-task))) ; dont forget '(...)' around 'some-task'

(def value (deref p)) ; blocking until promise is delivered
(println value)       ; 100 sweet !!!


(shutdown-agents) ; terminate threads
