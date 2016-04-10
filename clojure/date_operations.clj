(ns date_operations (:gen-class))
(import '(java.text SimpleDateFormat))  ; comes after 'ns' declaration


(def f (SimpleDateFormat. "yyyy-MM-dd"))
(def d (.parse f "2010-08-15"))
(println d) ; #inst "2010-08-14T23:00:00.000-00:00"

(import '(java.util GregorianCalendar))
(def gc (GregorianCalendar.))

(defn date [date-string])
(defn day-from [d])
