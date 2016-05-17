(ns test_java_jdbc
  (:gen-class)
  (:require [clojure.java.jdbc :as j]))


(defn -main [& args]
  (println "test_java_jdbc is running ...")

  (def db { :subprotocol "postgresql"
            :subname "//127.0.0.1:5432/test"
            :user "john"
            :password "john"})
  (with-db-connection [conn db]
    (let [rows (j/query conn ["SELECT * FROM FRUIT"])]
      (println (str rows)))))



