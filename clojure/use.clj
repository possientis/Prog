; use as opposed to require 
(ns org.currylogic.damages.http.expenses) ; defines current namespace

;(use 'org.danlarkin.json)  ; can;t find it on github
(use 'clojure.xml) ;; use, import, using, #include.. see require

(defn import-transactions-xml-from-bank [url]
  (let [xml-document (parse url)]
    ;; more code here
    ))

;;(defn totals-by-day [start-date end-date]
;;  (let [expenses-by-day (load-totals start-date end-date)]
;;        (encode-to-str expenses-by-day)))
