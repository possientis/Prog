(load "rat.scm")

(define (rat-test)
  ;;
  (define x (rat 3 2))
  (define y (rat 5 7))
  ;;
  (display "rat: starting unit test\n")
  ;;
  ;; numer and denom
  (let ((u (- (* (x 'numer) 2) (* (x 'denom) 3))))
    (if (not (= 0 u)) (display "rat: unit-test 1 failing\n")))
  (let ((u (- (* (y 'numer) 7) (* (y 'denom) 5))))
    (if (not (= 0 u)) (display "rat: unit-test 2 failing\n")))
  ;; '=
  (if (not (((rat-utils)'=) x (rat 3 2))) (display "rat: unit-test 3 failing\n"))
  (if (not (((rat-utils)'=) y (rat 5 7))) (display "rat: unit-test 4 failing\n"))
  ;; '+
  (let ((u (((rat-utils)'+) x y)))
    (if(not(((rat-utils)'=) u(rat 31 14)))(display "rat: unit-test 5 failing\n")))
  ;; '-
  (let ((u (((rat-utils)'-) x y)))
    (if(not(((rat-utils)'=) u(rat 11 14)))(display "rat: unit-test 6 failing\n")))
  ;; '*
  (let ((u (((rat-utils)'*) x y)))
    (if(not(((rat-utils)'=) u(rat 15 14)))(display "rat: unit-test 7 failing\n")))
  ;; '/
  (let ((u (((rat-utils)'/) x y)))
    (if(not(((rat-utils)'=) u(rat 21 10)))(display "rat: unit-test 8 failing\n")))




  (display "rat: unit test complete\n"))

(rat-test)
(quit)
