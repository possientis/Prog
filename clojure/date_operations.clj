(ns date_operations 
;  (:gen-class)
  (:import (java.text SimpleDateFormat)
           (java.util Calendar GregorianCalendar))
  (:require [clojure.string :as string]))

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


(defn to-string [date]
  (let [y (year-from date)
        m (+ 1 (month-from date))
        d (day-from date)]
    (string/join "-" [y m d])))

(println (to-string (date "2009-12-22")))

(def d (date "2009-10-31"))

(println (.add d Calendar/DAY_OF_MONTH 1))  ; nil

(println (to-string d))

(comment

(defn increment-day [d]
  (doto (.clone d) (.add Calendar/DAY_OF_MONTH 1)))


(defn increment-month [d]
  (doto (.clone d) (.add Calendar/MONTH 1)))


(defn increment-year [d]
  (doto (.clone d) (.add Calendar/YEAR 1)))

(defn decrement-day [d]
  (doto (.clone d) (.add Calendar/DAY_OF_MONTH -1)))


(defn decrement-month [d]
  (doto (.clone d) (.add Calendar/MONTH -1)))


(defn decrement-year [d]
  (doto (.clone d) (.add Calendar/YEAR -1)))
) ; comment

; refactoring
(defn date-operator [operation field]
  (fn [d]
    (doto (.clone d)
      (.add field (operation 1)))))

(def increment-day (date-operator + Calendar/DAY_OF_MONTH))
(def increment-month (date-operator + Calendar/MONTH))
(def increment-year (date-operator + Calendar/YEAR))
(def decrement-day (date-operator - Calendar/DAY_OF_MONTH))
(def decrement-month (date-operator - Calendar/MONTH))
(def decrement-year (date-operator - Calendar/YEAR))



