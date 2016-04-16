(ns expense_finders_test
  (:require [clojure.test :as test])
  (:use expense_finders stubbing))


(def all-expenses [(struct-map expense :amount 10.0 :date "2010-02-28")
                   (struct-map expense :amount 20.0 :date "2010-02-25")
                   (struct-map expense :amount 30.0 :date "2010-02-21")])


(test/deftest test-fetch-expenses-greater-than
  (stubbing [fetch-all-expenses all-expenses]
            (let [filtered (fetch-expenses-greater-than "" "" "" 15.0)]
              (test/is (= (count filtered) 2))
              (test/is (= (:amount (first filtered)) 20.0))
              (test/is (= (:amount (last filtered)) 30.0)))))

(comment

(println 
  (str 
    (macroexpand-1 
      '(stubbing [fetch-all-expenses all-expenses]
                 (let [filtered (fetch-expenses-greater-than "" "" "" 15.0)]
                   (test/is (= (count filtered) 2))
                   (test/is (= (:amount (first filtered)) 20.0))
                   (test/is (= (:amount (last filtered)) 30.0))))))) 

(binding [fetch-all-expenses (constantly all-expenses)] 
  (let [filtered (fetch-expenses-greater-than "" "" "" 15.0)] 
    (test/is (= (count filtered) 2)) 
    (test/is (= (:amount (first filtered)) 20.0)) 
    (test/is (= (:amount (last filtered)) 30.0))))

) ; comment




