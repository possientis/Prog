; require as opposed to use
; use, import, require, using, #include

(ns org.currylogic.damages.http.expenses) ; defines current namespace

;(require '(org.danlarkin [json :as json-lib]))
(require '(clojure [xml :as xml-core]))

(defn import-transactions-xml-from-bank [url]
  (let [xml-document (xml-core/parse url)]  ;; origin of 'parse' is now clear
    ;; more code here
    ))

;;(defn totals-by-day [start-date end-date]
;;  (let [expenses-by-day (load-totals start-date end-date)]
;;     (json-lib/encode-to-str expenses-by-day)))
