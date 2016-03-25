; vars are mutable data but not shared data. updated on a per-thread basis.

; special variables begin and end with an asterisk
(def ^:dynamic *db-host* "localhost") ; '*' usage indicate dynamic variable

(defn expense-report [start-date end-date]
  (println *db-host*))

(expense-report "2001-10-1" "2001-10-17")

; only visible to executing thread
(binding [*db-host* "production"]
  (expense-report "2001-10-1" "2001-10-17"))

(def ^:dynamic *other-var*) ; not specifiying any root binding

(println *other-var*) ; #<Unbound Unbound: #'user/*other-var*>


(def ^:dynamic *mysql-host*)  ; no root binding

(defn db-query [db]
  (binding [*mysql-host* db]
    (count *mysql-host*)))

(def mysql-hosts ["test-mysql" "dev-mysql" "staging-mysql"])

(println (pmap db-query mysql-hosts)) ; parallel map (using some thread pool) 
; each threads sees a different value of the binding *mysql-host*
(shutdown-agents) ; seems to be needed after pmap.




