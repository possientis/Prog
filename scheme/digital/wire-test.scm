(load "wire.scm")

(define (wire-test)
  ;; defining a few wires for testing
  (define a (wire))
  (define b (wire))
  (define c (wire))
  ;; defining a few actions for testing
  (define count1 0)     ; will test how many times proc1 runs
  (define count2 0)     ; will test how many times proc2 runs
  (define (proc1) (set! count1 (+ count1 1)))
  (define (proc2) (set! count2 (+ count2 1)))
  ;;
  (global 'unit-test-true!)    ; disables display of certain errors
  (global 'error-count-reset!) ; counter to check expected error do occur
  ;; start
  (display "wire: starting unit test\n")
  ;; testing get-signal following initialization
  (if (not (eq? '() (a 'get-signal))) (display "wire: unit-test 1 failing\n"))
  (if (not (eq? '() (b 'get-signal))) (display "wire: unit-test 2 failing\n"))
  (if (not (eq? '() (c 'get-signal))) (display "wire: unit-test 3 failing\n"))
  (if (not (eq? '() (a 'owner-tag))) (display "wire: unit-test 4 failing\n"))
  (if (not (eq? '() (b 'owner-tag))) (display "wire: unit-test 5 failing\n"))
  (if (not (eq? '() (c 'owner-tag))) (display "wire: unit-test 6 failing\n"))
  ;; testing set-signal! from '() to '() by 'x
  ((a 'set-signal!) '() 'x)
  ((b 'set-signal!) '() 'x)
  ((c 'set-signal!) '() 'x)
  (if (not (eq? '() (a 'get-signal))) (display "wire: unit-test 7 failing\n"))
  (if (not (eq? '() (b 'get-signal))) (display "wire: unit-test 8 failing\n"))
  (if (not (eq? '() (c 'get-signal))) (display "wire: unit-test 9 failing\n"))
  (if (not (eq? '() (a 'owner-tag)))(display "wire: unit-test 10 failing\n"))
  (if (not (eq? '() (b 'owner-tag)))(display "wire: unit-test 11 failing\n"))
  (if (not (eq? '() (c 'owner-tag)))(display "wire: unit-test 12 failing\n"))
  ;; testing set-signal! from '() to #f by 'x
  ((a 'set-signal!) #f 'x)
  ((b 'set-signal!) #f 'x)
  ((c 'set-signal!) #f 'x)
  (if (not (eq? #f (a 'get-signal))) (display "wire: unit-test 13 failing\n"))
  (if (not (eq? #f (b 'get-signal))) (display "wire: unit-test 14 failing\n"))
  (if (not (eq? #f (c 'get-signal))) (display "wire: unit-test 15 failing\n"))
  (if (not (eq? 'x (a 'owner-tag))) (display "wire: unit-test 16 failing\n"))
  (if (not (eq? 'x (b 'owner-tag))) (display "wire: unit-test 17 failing\n"))
  (if (not (eq? 'x (c 'owner-tag))) (display "wire: unit-test 18 failing\n"))
  ;; testing set-signal! from #f to #f by 'x
  ((a 'set-signal!) #f 'x)
  ((b 'set-signal!) #f 'x)
  ((c 'set-signal!) #f 'x)
  (if (not (eq? #f (a 'get-signal))) (display "wire: unit-test 19 failing\n"))
  (if (not (eq? #f (b 'get-signal))) (display "wire: unit-test 20 failing\n"))
  (if (not (eq? #f (c 'get-signal))) (display "wire: unit-test 21 failing\n"))
  (if (not (eq? 'x (a 'owner-tag))) (display "wire: unit-test 22 failing\n"))
  (if (not (eq? 'x (b 'owner-tag))) (display "wire: unit-test 23 failing\n"))
  (if (not (eq? 'x (c 'owner-tag))) (display "wire: unit-test 24 failing\n"))
  ;; testing set-signal! from #f to #f by 'y: it's ok no change required
  ((a 'set-signal!) #f 'y)  ; ownership will not change
  ((b 'set-signal!) #f 'y)
  ((c 'set-signal!) #f 'y)
  (if (not (eq? #f (a 'get-signal))) (display "wire: unit-test 25 failing\n"))
  (if (not (eq? #f (b 'get-signal))) (display "wire: unit-test 26 failing\n"))
  (if (not (eq? #f (c 'get-signal))) (display "wire: unit-test 27 failing\n"))
  (if (not (eq? 'x (a 'owner-tag))) (display "wire: unit-test 28 failing\n"))
  (if (not (eq? 'x (b 'owner-tag))) (display "wire: unit-test 29 failing\n"))
  (if (not (eq? 'x (c 'owner-tag))) (display "wire: unit-test 30 failing\n"))
  ;; testing set-signal! from #f to #t by 'y (this should fail)
  ((a 'set-signal!) #t 'y)
  ((b 'set-signal!) #t 'y)
  ((c 'set-signal!) #t 'y)
  (if (not (eq? #f (a 'get-signal))) (display "wire: unit-test 31 failing\n"))
  (if (not (eq? #f (b 'get-signal))) (display "wire: unit-test 32 failing\n"))
  (if (not (eq? #f (c 'get-signal))) (display "wire: unit-test 33 failing\n"))
  (if (not (eq? 'x (a 'owner-tag))) (display "wire: unit-test 34 failing\n"))
  (if (not (eq? 'x (b 'owner-tag))) (display "wire: unit-test 35 failing\n"))
  (if (not (eq? 'x (c 'owner-tag))) (display "wire: unit-test 36 failing\n"))
  (if(not(= 3 (global 'error-count)))(display "wire: unit-test 37 failing\n"))
  ;; testing set-signal! from #f to #t by 'x
  ((a 'set-signal!) #t 'x)
  ((b 'set-signal!) #t 'x)
  ((c 'set-signal!) #t 'x)
  (if (not (eq? #t (a 'get-signal))) (display "wire: unit-test 38 failing\n"))
  (if (not (eq? #t (b 'get-signal))) (display "wire: unit-test 39 failing\n"))
  (if (not (eq? #t (c 'get-signal))) (display "wire: unit-test 40 failing\n"))
  (if (not (eq? 'x (a 'owner-tag))) (display "wire: unit-test 41 failing\n"))
  (if (not (eq? 'x (b 'owner-tag))) (display "wire: unit-test 42 failing\n"))
  (if (not (eq? 'x (c 'owner-tag))) (display "wire: unit-test 43 failing\n"))
  ;; testing set-signal! from #t to #t by 'x
  ((a 'set-signal!) #t 'x)
  ((b 'set-signal!) #t 'x)
  ((c 'set-signal!) #t 'x)
  (if (not (eq? #t (a 'get-signal))) (display "wire: unit-test 44 failing\n"))
  (if (not (eq? #t (b 'get-signal))) (display "wire: unit-test 45 failing\n"))
  (if (not (eq? #t (c 'get-signal))) (display "wire: unit-test 46 failing\n"))
  (if (not (eq? 'x (a 'owner-tag))) (display "wire: unit-test 47 failing\n"))
  (if (not (eq? 'x (b 'owner-tag))) (display "wire: unit-test 48 failing\n"))
  (if (not (eq? 'x (c 'owner-tag))) (display "wire: unit-test 49 failing\n"))
  ;; testing set-signal! from #t to #t by 'y (it's ok no change required)
  ((a 'set-signal!) #t 'y)
  ((b 'set-signal!) #t 'y)
  ((c 'set-signal!) #t 'y)
  (if (not (eq? #t (a 'get-signal))) (display "wire: unit-test 50 failing\n"))
  (if (not (eq? #t (b 'get-signal))) (display "wire: unit-test 51 failing\n"))
  (if (not (eq? #t (c 'get-signal))) (display "wire: unit-test 52 failing\n"))
  (if (not (eq? 'x (a 'owner-tag))) (display "wire: unit-test 53 failing\n"))
  (if (not (eq? 'x (b 'owner-tag))) (display "wire: unit-test 54 failing\n"))
  (if (not (eq? 'x (c 'owner-tag))) (display "wire: unit-test 55 failing\n"))
  ;; testing set-signal! from #t to '() by 'y (should be ignored)
  ((a 'set-signal!) '() 'y)
  ((b 'set-signal!) '() 'y)
  ((c 'set-signal!) '() 'y)
  (if (not (eq? #t (a 'get-signal))) (display "wire: unit-test 56 failing\n"))
  (if (not (eq? #t (b 'get-signal))) (display "wire: unit-test 57 failing\n"))
  (if (not (eq? #t (c 'get-signal))) (display "wire: unit-test 58 failing\n"))
  (if (not (eq? 'x (a 'owner-tag))) (display "wire: unit-test 59 failing\n"))
  (if (not (eq? 'x (b 'owner-tag))) (display "wire: unit-test 60 failing\n"))
  (if (not (eq? 'x (c 'owner-tag))) (display "wire: unit-test 61 failing\n"))
  ;; testing set-signal! from #t to '() by 'x (ownership relinquished)
  ((a 'set-signal!) '() 'x)
  ((b 'set-signal!) '() 'x)
  ((c 'set-signal!) '() 'x)
  (if (not (eq? '() (a 'get-signal))) (display "wire: unit-test 62 failing\n"))
  (if (not (eq? '() (b 'get-signal))) (display "wire: unit-test 63 failing\n"))
  (if (not (eq? '() (c 'get-signal))) (display "wire: unit-test 64 failing\n"))
  (if (not (eq? '()(a 'owner-tag))) (display "wire: unit-test 65 failing\n"))
  (if (not (eq? '()(b 'owner-tag))) (display "wire: unit-test 66 failing\n"))
  (if (not (eq? '()(c 'owner-tag))) (display "wire: unit-test 67 failing\n"))
 ;; testing actions list
  (let ((list-a (a 'actions)))
    (if (not (eq? '() list-a)) (display "wire: unit-test 68 failing\n")))
  (let ((list-b (b 'actions)))
    (if (not (eq? '() list-b)) (display "wire: unit-test 69 failing\n")))
  (let ((list-c (c 'actions)))
    (if (not (eq? '() list-c)) (display "wire: unit-test 70 failing\n")))
  ;; testing test procedure counters still 0
  (if (not (= 0 count1)) (display "wire: unit-test 71 failing\n"))
  (if (not (= 0 count2)) (display "wire: unit-test 72 failing\n"))
  ;; testing add-actions adding proc1
  ((a 'add-action!) proc1)   ; proc1 should run once at this stage
  (if (not (= 1 count1)) (display "wire: unit-test 73 failing\n"))
  (let ((list-a (a 'actions)))
    (if (not (= 1 (length list-a))) (display "wire: unit-test 74 failing\n"))
    ((car list-a))  ; running proc1
    (if (not (= 2 count1)) (display "wire: unit-test 75 failing\n")))
  ;; testing set-signal! impact on proc1 from '() to '()
  ((a 'set-signal!) '() 'x)   ; should have no impact
  (if (not (= 2 count1)) (display "wire: unit-test 76 failing\n"))
  ;; testing set-signal! impact on proc1 from '() to #f
  ((a 'set-signal!) #f 'x)
  (if (not (= 3 count1)) (display "wire: unit-test 77 failing\n"))
   ;; testing set-signal! impact on proc1 from #f to #f
  ((a 'set-signal!) #f 'x)   ; should have no impact
  (if (not (= 3 count1)) (display "wire: unit-test 78 failing\n"))
  ;; testing set-signal! impact on proc1 from #f to #t by 'y
  ((a 'set-signal!) #t 'y)   ; should fail, proc1 should not run, new error
  (if (not (= 3 count1)) (display "wire: unit-test 79 failing\n"))
  (if(not(= 4 (global 'error-count)))(display "wire: unit-test 80 failing\n"))
  ;; testing set-signal! impact on proc1 from #f to #t by 'x
  ((a 'set-signal!) #t 'x)   ; proc1 should run since change of state
  (if (not (= 4 count1)) (display "wire: unit-test 81 failing\n"))
  ;; testing set-signal! impact on proc1 from #t to #t
  ((a 'set-signal!) #t 'x)   ; should have no impact
  (if (not (= 4 count1)) (display "wire: unit-test 82 failing\n"))
  ;; testing set-signal! impact on proc1 from #t to #f
  ((a 'set-signal!) #f 'x)   ; proc1 should run since change of state
  (if (not (= 5 count1)) (display "wire: unit-test 83 failing\n"))
  ;; testing set-signal! impact on proc1 from #f to '()
  ((a 'set-signal!) '() 'x)   ; proc1 should run since change of state
  (if (not (= 6 count1)) (display "wire: unit-test 84 failing\n"))
   ;; testing add-actions adding proc2
  ((a 'add-action!) proc2)   ; proc2 should run once at this stage
  (if (not (= 1 count2)) (display "wire: unit-test 85 failing\n"))
  (let ((list-a (a 'actions)))
    (if (not (= 2 (length list-a))) (print "wire: unit-test 86 failing"))
    ((car list-a))  ; running proc2
    (if (not (= 2 count2)) (display "wire: unit-test 87 failing\n"))
    ((cadr list-a)) ; running proc1
    (if (not (= 7 count1)) (display "wire: unit-test 88 failing\n")))
  ;; testing set-signal! impact on proc1 & proc2 from '() to '()
  ((a 'set-signal!) '() 'x)   ; should have no impact
  (if (not (= 7 count1)) (display "wire: unit-test 89 failing\n"))
  (if (not (= 2 count2)) (display "wire: unit-test 90 failing\n"))
   ;; testing set-signal! impact on proc1 & proc2 from '() to #f
  ((a 'set-signal!) #f 'x)
  (if (not (= 8 count1)) (display "wire: unit-test 91 failing\n"))
  (if (not (= 3 count2)) (display "wire: unit-test 92 failing\n"))
  ;; testing set-signal! impact on proc1 & proc2 from #f to #f
  ((a 'set-signal!) #f 'x)
  (if (not (= 8 count1)) (display "wire: unit-test 93 failing\n"))
  (if (not (= 3 count2)) (display "wire: unit-test 94 failing\n"))
  ;; testing set-signal! impact on proc1 & proc2 from #f to #t by 'y
  ((a 'set-signal!) #t 'y)   ; should fail, one more error
  (if (not (= 8 count1)) (display "wire: unit-test 95 failing\n"))
  (if (not (= 3 count2)) (display "wire: unit-test 96 failing\n"))
  (if(not(= 5 (global 'error-count)))(display "wire: unit-test 97 failing\n"))
   ;; testing set-signal! impact on proc1 & proc2 from #f to #t
  ((a 'set-signal!) #t 'x)   ; proc1 and proc2 should run on change of state
  (if (not (= 9 count1)) (display "wire: unit-test 98 failing\n"))
  (if (not (= 4 count2)) (display "wire: unit-test 99 failing\n"))
  ;; testing set-signal! impact on proc1 & proc2 from #t to #t
  ((a 'set-signal!) #t 'x)   ; no impact
  (if (not (= 9 count1)) (display "wire: unit-test 100 failing\n"))
  (if (not (= 4 count2)) (display "wire: unit-test 101 failing\n"))
  ;; testing set-signal! impact on proc1 & proc2 from #t to '()
  ((a 'set-signal!) '() 'x)   ; proc1 and proc2 should run
  (if (not (= 10 count1)) (display "wire: unit-test 102 failing\n"))
  (if (not (= 5 count2)) (display "wire: unit-test 103 failing\n"))

  ;; exiting: restoring global variables
  (global 'unit-test-false!)
  (global 'error-count-reset!)
  (display "wire: unit test complete\n"))

(wire-test)
(exit 0)
