(load "source.scm")

(define (source-test)
  (define a (wire))     ; creating wire for testing
  ;;
  (global 'unit-test-true!) ; disables display of certain errors
  (global 'error-count-reset!);
  ;; start
  (display "source: starting unit test\n")
  ;; checking interface for setting source signal
  (let ((s (source a)))
    ;; checking internal state after initialization
    (if(not(eq? '()(s 'signal)))(display "source: unit-test 1 failing\n"))
    ;; checking from '() to '()
    (s '())
    (if(not(eq? '()(s 'signal)))(display "source: unit-test 2 failing\n"))
    ;; checking from '() to #f
    (s #f)
    (if(not(eq? #f (s 'signal)))(display "source: unit-test 3 failing\n"))
    ;; checking from #f to #f
    (s #f)
    (if(not(eq? #f (s 'signal)))(display "source: unit-test 4 failing\n"))
    ;; checking from #f to #t
    (s #t)
    (if(not(eq? #t (s 'signal)))(display "source: unit-test 5 failing\n"))
    ;; checking from #t to #t
    (s #t)
    (if(not(eq? #t (s 'signal)))(display "source: unit-test 6 failing\n"))
    ;; checking from #t to '()
    (s '())
    (if(not(eq? '()(s 'signal)))(display "source: unit-test 7 failing\n"))
    ;; checking wire state
    ;; neutral source
    (begin (s '()) (global 'propagate!))
    (if (not (eq? '() (a 'get-signal))) (display "source: unit-test 8 failing\n"))
    ;; negative source
    (begin (s #f) (global 'propagate!))
    (if (not (eq? #f (a 'get-signal))) (display "source: unit-test 9 failing\n"))
    ;; positive source
    (begin (s #t) (global 'propagate!))
    (if (not (eq? #t (a 'get-signal))) (display "source: unit-test 10 failing\n"))
    ;; back to neutral source
    (begin (s '()) (global 'propagate!))
    (if(not (eq? '() (a 'get-signal))) (display "source: unit-test 11 failing\n"))
    ;;
    ;; impact of changing wire signal when connected to neutral source
    (begin (s '()) (global 'propagate!)) ; attempt to change wire state should succeed
    ;;
    ;; changing to '()
    (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
    (if(not (eq? '() (a 'get-signal))) (display "source: unit-test 12 failing\n"))
    ;; changing to #f
    (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
    (if(not (eq? #f (a 'get-signal))) (display "source: unit-test 13 failing\n"))
    ;; changing to #t
    (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
    (if(not (eq? #t (a 'get-signal))) (display "source: unit-test 14 failing\n"))
    ;; changing back to '()
    (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
    (if(not (eq? '() (a 'get-signal))) (display "source: unit-test 15 failing\n"))
    ;;
    ;; impact of changing wire signal when connected to negative source
    (begin (s #f) (global 'propagate!)) ; attempt to change wire state should fail
    ;;
    ;; changing to '()
    (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
    (if(not (eq? #f (a 'get-signal))) (display "source: unit-test 16 failing\n"))
    ;; changing to #f
    (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
    (if(not (eq? #f (a 'get-signal))) (display "source: unit-test 17 failing\n"))
    ;; changing to #t (this should not only fail, but also produce error)
    (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
    (if(not (eq? #f (a 'get-signal))) (display "source: unit-test 18 failing\n"))
    (if(not(= 1 (global 'error-count)))(display "source unit-test 19 failing\n"))
    ;; changing back to '()
    (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
    (if(not (eq? #f (a 'get-signal))) (display "source: unit-test 20 failing\n"))
    ;;
    ;; impact of changing wire signal when connected to positive source
    (begin (s #t) (global 'propagate!)) ; attempt to change wire state should fail
    ;;
    ;; changing to '()
    (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
    (if(not (eq? #t (a 'get-signal))) (display "source: unit-test 21 failing\n"))
    ;; changing to #t
    (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
    (if(not (eq? #t (a 'get-signal))) (display "source: unit-test 22 failing\n"))
    ;; changing to #f (this should not only fail, but also produce error)
    (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
    (if(not (eq? #t (a 'get-signal))) (display "source: unit-test 23 failing\n"))
    (if(not(= 2 (global 'error-count)))(display "source unit-test 24 failing\n"))
    ;; changing back to '()
    (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
    (if(not (eq? #t (a 'get-signal))) (display "source: unit-test 25 failing\n")))
  ;; exiting
  (global 'time-reset!)
  (global 'unit-test-false!)
  (global 'error-count-reset!)
  (display "source: unit test complete\n"))

(source-test)
(quit)
