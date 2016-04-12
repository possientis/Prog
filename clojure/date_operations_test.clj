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
    (is (= (to-string d) "2009-01-22"))))



(println (str (macroexpand-1 
                '(deftest test-simple-data-parsing 
                   (let [d (date "2009-1-22")]
                     (is (= (day-from d) 22)))))))

(comment
(def test-simple-data-parsing 
  (fn [] (test-var (var test-simple-data-parsing))))
)


(run-tests 'date_operations_test)

