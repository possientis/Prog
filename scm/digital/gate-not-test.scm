(load "gate-not.scm")

(define (gate-not-test)
  ;;
  (define in (wire))
  (define out (wire))
  (define earth (wire))
  (define power (wire))
  ;;
  (display "gate-not: starting unit test\n")
  ;;
  ;; setting up power supply
  ((earth 'set-signal!) #f 'x)
  ((power 'set-signal!) #t 'x)
  ;;
  ;; connecting in and out to gate
  (gate-not in out earth power)
  ;;
  ;; setting system in initial condition
  ((in 'set-signal!) #t 'x)
  (global 'propagate!)
  ;;
  ;; testing initial condition
  (if (not (eq? #t (in 'get-signal))) (display "gate-not: unit-test 1 failing\n"))
  (if (not (eq? #f (out 'get-signal))) (display "gate-not: unit-test 2 failing\n"))
  ;; transition #t -> #t
  ((in 'set-signal!) #t 'x)
  (global 'propagate!)
  (if (not (eq? #t (in 'get-signal))) (display "gate-not: unit-test 3 failing\n"))
  (if (not (eq? #f (out 'get-signal))) (display "gate-not: unit-test 4 failing\n"))
  ;; transition #t -> #f
  ((in 'set-signal!) #f 'x)
  (global 'propagate!)
  (if (not (eq? #f (in 'get-signal))) (display "gate-not: unit-test 5 failing\n"))
  (if (not (eq? #t (out 'get-signal))) (display "gate-not: unit-test 6 failing\n"))
  ;; transition #f -> #f
  ((in 'set-signal!) #f 'x)
  (global 'propagate!)
  (if (not (eq? #f (in 'get-signal))) (display "gate-not: unit-test 7 failing\n"))
  (if (not (eq? #t (out 'get-signal))) (display "gate-not: unit-test 8 failing\n"))
  ;; transition #f -> #t
  ((in 'set-signal!) #t 'x)
  (global 'propagate!)
  (if (not (eq? #t (in 'get-signal))) (display "gate-not: unit-test 9 failing\n"))
  (if (not (eq? #f (out 'get-signal)))(display "gate-not: unit-test 10 failing\n"))
  ;;
  (display "gate-not: unit test complete\n"))

(gate-not-test)
(quit)
