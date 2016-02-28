; special variables begin and end with an asterisk
(def ^:dynamic *db-host* "localhost") ; '*' usage indicate dynamic variable

(defn expense-report [start-date end-date]
  (println *db-host*))

(expense-report "2001-10-1" "2001-10-17")

(binding [*db-host* "production"]
  (expense-report "2001-10-1" "2001-10-17"))


