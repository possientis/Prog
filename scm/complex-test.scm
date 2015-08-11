(load "complex.scm")

(define (complex-test)
  ;;
  (define pi 3.141592653589793) ;; not defined in mit-scheme
  ;;
  (define x0 (complex 1 1))
  (define x1 (complex 4 3))
  (define x2 (complex 1 0))
  (define x3 (complex 0 1))
  (define x4 (complex -1 0))
  (define x5 (complex 0 -1))
  ;;
  (display "complex: starting unit testin\n")
  ;;
  ;; real and imag
  (if (not (= 4 (x1 'real))) (display "complex: unit test 1 failing\n"))
  (if (not (= 1 (x0 'real))) (display "complex: unit test 2 failing\n"))
  (if (not (= 3 (x1 'imag))) (display "complex: unit test 3 failing\n"))
  (if (not (= 1 (x0 'imag))) (display "complex: unit test 4 failing\n"))
  ;; '+
  (let ((u (((complex-utils)'+) x0 x1)))
    (if (not (= 5 (u 'real))) (display "complex: unit testing 5 failing\n"))
    (if (not (= 4 (u 'imag))) (display "complex: unit testing 6 failing\n")))
  ;; '-
  (let ((u (((complex-utils)'-) x1 x0)))
    (if (not (= 3 (u 'real))) (display "complex: unit testing 7 failing\n"))
    (if (not (= 2 (u 'imag))) (display "complex: unit testing 8 failing\n")))
  ;; '*
  (let ((u (((complex-utils)'*) x1 x0)))
    (if (not (= 1 (u 'real))) (display "complex: unit testing 7 failing\n"))
    (if (not (= 7 (u 'imag))) (display "complex: unit testing 8 failing\n")))
  ;; mod
  (if (not (= 5 (x1 'mod))) (display "complex: unit testing 9 failing\n"))
  ;; angle






  (display "complex: unit test complete\n"))

(complex-test)
(quit)
