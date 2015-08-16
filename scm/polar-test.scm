(load "polar.scm")

(define (polar-test)
  ;;
  (define pi 3.141592653589793) ;; not defined in mit-scheme
  (define (same? x y)
    (< (abs (- x y)) 0.000000001))
  ;;
  (define x0 (polar (sqrt 2) (/ 3.141592653589793 4)))
  (define x1 (polar 5 (atan 3 4)))
  (define x2 (polar 1 0))
  (define x3 (polar 1 (/ 3.141592653589793 2)))
  (define x4 (polar 1 3.141592653589793))
  (define x5 (polar 1 (* 1.5 3.141592653589793)))
  ;;
  (display "polar: starting unit test\n")
  ;;
  ;; mod and angle
  (if (not (same? (sqrt 2) (x0 'mod))) (display "polar: unit test 1 failing\n"))
  (if (not (same? 5 (x1 'mod))) (display "polar: unit test 2 failing\n"))
  (if (not (same? (cos (x0 'angle)) (cos (/ pi 4))))
    (display "polar: unit test 3 failing\n"))
  (if (not (same? (sin (x0 'angle)) (sin (/ pi 4))))
    (display "polar: unit test 4 failing\n"))
  (if (not (same? (cos (x1 'angle)) (cos (atan 3 4))))
    (display "polar: unit test 5 failing\n"))
  (if (not (same? (sin (x1 'angle)) (sin (atan 3 4))))
    (display "polar: unit test 6 failing\n"))
  ;; '+
  (let ((u (((polar-utils)'+) x0 x1)))
    (if (not (same? 5 (u 'real))) (display "polar: unit test 7 failing\n"))
    (if (not (same? 4 (u 'imag))) (display "polar: unit test 8 failing\n")))
  ;; '-
  (let ((u (((polar-utils)'-) x1 x0)))
    (if (not (same? 3 (u 'real))) (display "polar: unit test 9 failing\n"))
    (if (not (same? 2 (u 'imag))) (display "polar: unit test 10 failing\n")))
  ;; '*
  (let ((u (((polar-utils)'*) x1 x0)))
    (if (not (same? 1 (u 'real))) (display "polar: unit test 11 failing\n"))
    (if (not (same? 7 (u 'imag))) (display "polar: unit test 12 failing\n")))
  ;; '/ and '=
  (let ((u (((polar-utils)'/) x1 x0)))
    (let ((v (((polar-utils)'*) u x0)))
      (if(not(((polar-utils)'=)v x1))(display"complex: unit test 13 failing\n"))
      ))
  ;; real and imag


  (display "polar: unit test complete\n"))

(polar-test)
(quit)

