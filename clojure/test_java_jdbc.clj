(ns test_java_jdbc
  (:gen-class)
  (:require [clojure.java.jdbc :as j]))

(def mysql-db {:subprotocol "postgres"
               :subname "//127.0.0.1:3306/test"
               :user "john"
               :password ""})

(j/insert! mysql-db :fruit
             {:name "Apple" :appearance "rosy" :cost 24}
             {:name "Orange" :appearance "round" :cost 49})


(defn -main [& args]
  (println "test_java_jdbc is running ...")
  (println mysql-db))



