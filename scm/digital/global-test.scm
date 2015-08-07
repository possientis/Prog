(load "global.scm")

(define (global-test)
  (define a (make-global-object))
  (define b (make-global-object))


  (display "global: starting unit test\n")

  ;; unit-test?
  (if (not (eq? (a 'unit-test?) #f)) (display "global: unit-test 1 failing\n"))
  (if (not (eq? (b 'unit-test?) #f)) (display "global: unit-test 2 failing\n"))
  (a 'unit-test-true!)  ; this should impact b
  (if (not (eq? (a 'unit-test?) #t)) (display "global: unit-test 3 failing\n"))
  (if (not (eq? (b 'unit-test?) #t)) (display "global: unit-test 4 failing\n"))
  (b 'unit-test-false!)  ; this should impact a
  (if (not (eq? (a 'unit-test?) #f)) (display "global: unit-test 5 failing\n"))
  (if (not (eq? (b 'unit-test?) #f)) (display "global: unit-test 6 failing\n"))
  ;; debug?
  (if (not (eq? (a 'debug?) #f)) (display "global: unit-test 7 failing\n"))
  (if (not (eq? (b 'debug?) #f)) (display "global: unit-test 8 failing\n"))
  (a 'debug-true!)  ; this should impact b
  (if (not (eq? (a 'debug?) #t)) (display "global: unit-test 9 failing\n"))
  (if (not (eq? (b 'debug?) #t)) (display "global: unit-test 10 failing\n"))
  (b 'debug-false!)  ; this should impact a
  (if (not (eq? (a 'debug?) #f)) (display "global: unit-test 11 failing\n"))
  (if (not (eq? (b 'debug?) #f)) (display "global: unit-test 12 failing\n"))
  ;; error-count
  (if (not (= (a 'error-count) 0)) (display "global: unit-test 13 failing\n"))
  (if (not (= (b 'error-count) 0)) (display "global: unit-test 14 failing\n"))
  ((a 'error!) "")  ; should increase counter by 1 for both a and b
  (if (not (= (a 'error-count) 1)) (display "global: unit-test 15 failing\n"))
  (if (not (= (b 'error-count) 1)) (display "global: unit-test 16 failing\n"))
  ((b 'error!) "")  ; should increase counter by 1 for both a and b
  (if (not (= (a 'error-count) 2)) (display "global: unit-test 17 failing\n"))
  (if (not (= (b 'error-count) 2)) (display "global: unit-test 18 failing\n"))
  (a 'error-count-reset!) ; impacts b
  (if (not (= (a 'error-count) 0)) (display "global: unit-test 19 failing\n"))
  (if (not (= (b 'error-count) 0)) (display "global: unit-test 20 failing\n"))
  ;; main-agenda
  (if (not (= (a 'now) 0)) (display "global: unit-test 21 failing\n"))
  (if (not (= (b 'now) 0)) (display "global: unit-test 22 failing\n"))
  ((a 'add-event!) 1 (lambda () 'done)) ; impacts b
  (if (not (= (a 'now) 0)) (display "global: unit-test 22 failing\n"))
  (if (not (= (b 'now) 0)) (display "global: unit-test 23 failing\n"))
  (b 'propagate!)   ; this should move the clock of both a and b
  (if (not (= (a 'now) 1)) (display "global: unit-test 24 failing\n"))
  (if (not (= (b 'now) 1)) (display "global: unit-test 25 failing\n"))
  ((b 'add-event!) 3 (lambda () 'done)) ; impacts a
  (a 'propagate!)   ; this should move the clock of both a and b
  (if (not (= (a 'now) 4)) (display "global: unit-test 26 failing\n"))
  (if (not (= (b 'now) 4)) (display "global: unit-test 27 failing\n"))
  (a 'time-reset!)  ; impacts b
  (if (not (= (a 'now) 0)) (display "global: unit-test 28 failing\n"))
  (if (not (= (b 'now) 0)) (display "global: unit-test 29 failing\n"))

  (display "global: unit test complete\n"))

(global-test)
(quit)
