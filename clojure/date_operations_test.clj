; unit test

(ns date_operations_test 
;  (:gen-class)
  (:use clojure.test)
  (:use date_operations))

(deftest test-simple-data-parsing
  (let [d (date "2009-1-22")]
    (is (= (day-from d) 22))
    (is (= (month-from d) 0))   ; Jan -> 0
    (is (= (year-from d) 2009))))

(deftest test-to-string 
  (let [d (date "2009-1-22")]
    (is (= (to-string d) "2009-1-22"))))

(deftest test-incrementing
  (let [d (date "2009-10-31")
        n-day (increment-day d)
        n-month (increment-month d)
        n-year (increment-year d)] 
    (is (= (to-string n-day) "2009-11-1"))
    (is (= (to-string n-month) "2009-11-30"))
    (is (= (to-string n-year) "2010-10-31"))))

(deftest test-decrementing-date
  (let [d (date "2009-11-01")
        n-day (decrement-day d)
        n-month (decrement-month d)
        n-year (decrement-year d)]
    (is (= (to-string n-day) "2009-10-31"))
    (is (= (to-string n-month) "2009-10-1"))
    (is (= (to-string n-year) "2008-11-1"))))




(println (str (macroexpand-1 
                '(deftest test-simple-data-parsing 
                   (let [d (date "2009-1-22")]
                     (is (= (day-from d) 22)))))))

(comment
(def test-simple-data-parsing 
  (fn [] (test-var (var test-simple-data-parsing))))
)


(run-tests 'date_operations_test)

