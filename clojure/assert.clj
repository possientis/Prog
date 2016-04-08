; assert macro
(defmacro assert-true [test-expr]
  (let [[operator lhs rhs] test-expr]
    `(let [lhsv# ~lhs rhsv# ~rhs ret# ~test-expr]
       (if-not ret#
         (throw (RuntimeException. (str '~lhs " is not " '~operator " " rhsv#)))
         true))))

(println (str (macroexpand-1 '(assert-true (= x 2)))))

(comment
(let [lhsv__1__auto__   x 
      rhsv__2__auto__   2 
      ret__3__auto__    (= x 2)] 
  (if-not ret__3__auto__ 
    (throw (java.lang.RuntimeException. (str (quote x) " is not " (quote =) " " rhsv__2__auto__))) 
    true))
)

(def x 2)
(assert-true (= x 2))
(assert-true (= 2 x))
;(assert-true (= x 3)) ; throw exception


(println (str (macroexpand-1 '(assert-true (> 5 1)))))
(comment
(let [lhsv__1__auto__   5 
      rhsv__2__auto__ 1 
      ret__3__auto__ (> 5 1)] 
  (if-not ret__3__auto__ 
    (throw (java.lang.RuntimeException. (str (quote 5) " is not " (quote >) " " rhsv__2__auto__))) 
    true))
)

(assert-true (> 5 1))


