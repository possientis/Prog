(load "complex.scm")

(define (complex-test)
  ;;
  (define pi 3.141592653589793) ;; not defined in mit-scheme
  (define (same? x y)
    (< (abs (- x y)) 0.000000001))
  ;;
  (define x0 (complex 1 1))
  (define x1 (complex 4 3))
  (define x2 (complex 1 0))
  (define x3 (complex 0 1))
  (define x4 (complex -1 0))
  (define x5 (complex 0 -1))
  ;;
  (display "complex: starting unit test\n")
  ;;
  ;; real and imag
  (if (not (= 4 (x1 'real))) (display "complex: unit test 1 failing\n"))
  (if (not (= 1 (x0 'real))) (display "complex: unit test 2 failing\n"))
  (if (not (= 3 (x1 'imag))) (display "complex: unit test 3 failing\n"))
  (if (not (= 1 (x0 'imag))) (display "complex: unit test 4 failing\n"))
  ;; '+
  (let ((u (((complex-utils)'+) x0 x1)))
    (if (not (= 5 (u 'real))) (display "complex: unit test 5 failing\n"))
    (if (not (= 4 (u 'imag))) (display "complex: unit test 6 failing\n")))
  ;; '-
  (let ((u (((complex-utils)'-) x1 x0)))
    (if (not (= 3 (u 'real))) (display "complex: unit test 7 failing\n"))
    (if (not (= 2 (u 'imag))) (display "complex: unit test 8 failing\n")))
  ;; '*
  (let ((u (((complex-utils)'*) x1 x0)))
    (if (not (= 1 (u 'real))) (display "complex: unit test 8.1 failing\n"))
    (if (not (= 7 (u 'imag))) (display "complex: unit test 8.2 failing\n")))
  ;; '/ and '=
  (let ((u (((complex-utils)'/) x1 x0)))
    (let ((v (((complex-utils)'*) u x0)))
      (if(not(((complex-utils)'=)v x1))(display"complex: unit test 8.3 failing\n"))
      ))
  ;; mod
  (if (not (= 5 (x1 'mod))) (display "complex: unit test 9 failing\n"))
  ;; angle
  (if (not(same?(x0 'angle)(/ pi 4)))(display "complex: unit test 10 failing\n"))
  (if (not(same?(x2 'angle) 0))(display "complex: unit test 11 failing\n"))
  (if (not(same?(x3 'angle)(/ pi 2)))(display "complex: unit test 12 failing\n"))
  (if (not(same?(x4 'angle)(/ pi 1)))(display "complex: unit test 13 failing\n"))
  (if (not(same?(x5 'angle)(-(/ pi 2))))(display"complex: unit test 14 failing\n"))


  (display "complex: unit test complete\n"))

(complex-test)
(quit)
