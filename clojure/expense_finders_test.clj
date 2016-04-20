(ns expense_finders_test
  (:gen-class)
  (:require [clojure.test :as test])
  (:use expense_finders stubbing))


(def all-expenses [(struct-map expense :amount 10.0 :date "2010-02-28")
                   (struct-map expense :amount 20.0 :date "2010-02-25")
                   (struct-map expense :amount 30.0 :date "2010-02-21")])

(defmocktest test-fetch-expenses-greater-than
  (stubbing [fetch-all-expenses all-expenses]
            (let [filtered (fetch-expenses-greater-than "" "" "" 15.0)]
              (test/is (= (count filtered) 2))
              (test/is (= (:amount (first filtered)) 20.0))
              (test/is (= (:amount (last filtered)) 30.0)))))


(defmocktest test-filter-expenses-greater-than
  (mocking [log-call]
            (let [filtered (expenses-greater-than all-expenses 15.0)]
              (test/is (= (count filtered) 2))
              (test/is (= (:amount (first filtered)) 20.0))
              (test/is (= (:amount (last filtered)) 30.0))
              (verify-call-times-for log-call 1)
              (verify-first-call-args-for log-call "expenses-greater-than" 15.0)
              (verify-nth-call-args-for 1 log-call "expenses-greater-than" 15.0))))

(defn -main []
  (test/run-tests 'expense_finders_test))

(-main)
