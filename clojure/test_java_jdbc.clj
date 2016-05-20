; the purpose of this file is to demonstrate the use of the clojure library
; java.jdbc which is based on java's JDBC. See file JDBCExample2.java for
; an example of use in java. We are now focussing on closure.

; the call to the ns macro below defines a namespace of the same name as the file
; the :gen-class directive ensures that a .class file is generated so we can call 
; java. Note that we have a -main procedure defined below as an entry point to 
; the program. the key here is the :require directive which creates dependency 
; to clojure.java.jdbc. As this library is not in the standard clojure jar file,
; we have two choices:
;
; 1. is to create a new clojure jar file (see run.sh about this).
;
; 2. A far simpler solution is to create a path ./clojure/java containing the 
; source file jdbc.clj (which itself defines the name space clojure.java.jdbc)
;
; COMPILATION is then very simply achieved as follows:
;
; $ clojurec test_java_jdbc
;
; note that the compiler clojurec expects no extension '.clj' in the file name
; i.e. it is looking for the namespace. 
;
; In order to run the program, WE CANNOT simply use the usual java command:
;
; $ java -cp .:/usr/share/java/clojure-1.6.0.jar test_java_jdbc
;
; We need to INCLUDE the postgresql driver jar (with of course '.:')
; 
; $ java -cp \
; .:/usr/share/java/clojure-1.6.0.jar:/usr/share/java/postgresql-jdbc4.jar \
; test_java_jdbc
;

(ns test_java_jdbc
  (:gen-class)
  (:require [clojure.java.jdbc :as j]))

(def db { :subprotocol "postgresql"
          :subname "//127.0.0.1:5432/test"
          :user "john"
          :password "john"})


(defn -main [& args]
  (println "test_java_jdbc is running ...")

    (j/with-db-connection [conn db]
    (let [rows (j/query conn ["SELECT * FROM FRUIT"])]
      (println (first rows)))))






