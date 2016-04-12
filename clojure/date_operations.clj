(ns date_operations 
;  (:gen-class)
  (:import (java.text SimpleDateFormat)
           (java.util Calendar GregorianCalendar)
           (clojure.contrib.str-utils)))

; we did import within ns declaration
;(import '(java.text SimpleDateFormat))  ; comes after 'ns' declaration
;(import '(java.util GregorianCalendar))

(def f (SimpleDateFormat. "yyyy-MM-dd"))
(def d (.parse f "2010-08-15"))
(println d) ; #inst "2010-08-14T23:00:00.000-00:00"


(def gc (GregorianCalendar.))
(println (.setTime gc d))

(println "gc = " gc)

(defn date [date-string]
  (let [f (SimpleDateFormat. "yyyy-MM-dd")
        d (.parse f date-string)]
    (doto (GregorianCalendar.)
      (.setTime d))))

(println (date "2010-08-15"))

(println (.get gc Calendar/DAY_OF_MONTH))




(defn day-from [d]
  (.get d Calendar/DAY_OF_MONTH))

(println (day-from gc))

(defn month-from [d]
  (.get d Calendar/MONTH))

(defn year-from [d]
  (.get d Calendar/YEAR))

(println (month-from (date "2009-12-22")))


