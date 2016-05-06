(ns test_java_jdbc
  (:gen-class)
  (:require [clojure.java.jdbc :as j]))



(defn -main [& args]
  (println "test_java_jdbc is running ...")
  (println "args = " (str args)))



