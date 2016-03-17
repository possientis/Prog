; calling clojure code from java
; this called is being called from java Driver.java
(ns clj.script.example)

(defn print-report [user-name]
  (println "Report for:" user-name)
  10)
