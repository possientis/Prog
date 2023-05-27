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
; $ java -cp /usr/share/java/clojure-1.6.0.jar:. test_java_jdbc
;
; We need to INCLUDE the postgresql driver jar
; 
; $ java -cp \
; /usr/share/java/clojure-1.6.0.jar:/usr/share/java/postgresql.jar:. \
; test_java_jdbc
;
; be careful with lazy evaluation, if you attempt to get results
; after a connection is closed....

(ns test_java_jdbc
  (:gen-class)
  (:require [clojure.java.jdbc :as j])
  (:require [clojure.string :as s]))


(defn db [user] 
  { :subprotocol  "postgresql"
     :subname      (str "//127.0.0.1:5432/" user) ; port number is optional
     :user         user
     :password     user })

(defn create-table [conn]
  (let [sql (str "CREATE  TABLE COMPANY ("
                 "ID      INT PRIMARY KEY NOT NULL,"
                 "NAME    TEXT            NOT NULL,"
                 "AGE     INT             NOT NULL,"
                 "ADDRESS CHAR(50)                ,"
                 "SALARY  REAL                    );")]
    (j/execute! conn [sql])))

(defn delete-table [conn]
  (let [sql "DROP TABLE COMPANY;"]
    (j/execute! conn [sql])))


; clojure has syntax for destructuring, which is not used here 
(defn display-item [item]
  (println (str "ID: "          (:id item)
                ",\tNAME: "     (:name item)
                ",\tAGE: "      (:age item)
                ",\tADDRESS: "  (s/trim (:address item))
                ",\tSALARY: "   (:salary item))))

(defn query-table [conn]
  (let [rows (j/query conn ["SELECT * FROM COMPANY;"])]
    (dorun
      (for [item rows]
        (display-item item)))))


(defn -main [& args]

  (println "test_java_jdbc is running ...")

  (j/with-db-connection [conn (db (nth args 0))]
    (create-table conn)

    (let [item {:id 1 :name "Paul" :age 32 :address "California" :salary 20000.0}]
      (j/insert! conn :company item))

    (let [item {:id 2 :name "Allen" :age 25 :address "Texas" :salary 15000.0}]
      (j/insert! conn :company item))

    (let [item {:id 3 :name "Teddy" :age 23 :address "Norway" :salary 20000.0}]
      (j/insert! conn :company item))

    (let [item {:id 4 :name "Mark" :age 25 :address "Rich-Mond" :salary 65000.0}]
      (j/insert! conn :company item))

    (query-table conn)

    (println "updating salary to 25,000 for id = 1 ...")

    (j/update! conn :company {:salary 25000.0} ["id=?" 1])

    (query-table conn)

    (println "deleting entry with id = 2 ...")

    (j/delete! conn :company ["id=?" 2])

    (query-table conn)

    (delete-table conn)
  )
)
