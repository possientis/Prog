; the purpose of this file is to demonstrate the use of the clojure library ; java.jdbc which is based on java's JDBC. See file JDBCExample2.java for
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

; be careful with lazy evaluation, if you attempt to get results
; after a connection is closed....


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
      (let [rows (j/query conn ["SELECT * FROM FRUIT WHERE NAME=?" "Apple"])]
        (println (first rows))) ;{:cost 24, :appearance rosy, :name Apple, :id 1} 
      (let [rows (j/query conn 
                          ; specifies function to be applied to each row
                          ["SELECT * FROM FRUIT WHERE ID=?" 1] {:row-fn :name})]
        (println rows)) ; (Apple)
      (j/insert! conn :fruit {:cost 12, :appearance "blue", :name "Pear", :id 2})
      (j/update! conn :fruit {:appearance "green"} ["id=?" 2])
      ;(j/delete! conn :fruit ["id=?" 2])
      (j/execute! conn ["DELETE FROM FRUIT WHERE ID=?" 2])  ; generic sql
      ))








