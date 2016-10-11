(load "agenda.scm")

(define (agenda-test)
  ;; defining agendas for testing
  (define a (agenda))
  (define b (agenda))
  ;;
  (define count 0)  ;; will allow checking of procedure execution
  ;; Order of execution of these procedure should lead to different counter
  (define (pra1) (set! count (+ 1 (* 2 count))))
  (define (pra2) (set! count (+ 3 (* 5 count))))
  (define (pra3) (set! count (+ 7 (* 11 count))))
  (define (pra4) (set! count (+ 13 (* 17 count))))
  (define (prb1) (set! count (+ 2 (* 11 count))))
  (define (prb2) (set! count (+ 3 (* 17 count))))
  (define (prb3) (set! count (+ 5 (* 3 count))))
  (define (prb4) (set! count (+ 7 (* 2 count))))

  ;; start
  (display "agenda: starting unit test\n")
  ;; testing state following initialization
  (if (not (a 'isempty?)) (display "agenda: unit-test 1 failing\n"))
  (if (not (b 'isempty?)) (display "agenda: unit-test 2 failing\n"))
  (if (not (zero? (a 'time))) (display "agenda: unit-test 3 failing\n"))
  (if (not (zero? (b 'time))) (display "agenda: unit-test 4 failing\n"))
  ;; testing private method new-queue
  (let ((nqa ((a 'debug) 'new-queue)) (nqb ((b 'debug) 'new-queue)))
    (let((sa1(nqa 23 pra1))(sa2(nqa 7 pra2))(sb1(nqb 13 prb1))(sb2(nqb 5 prb2)))
      (let ((qa1 (cdr sa1)) (qa2 (cdr sa2)) (qb1 (cdr sb1)) (qb2 (cdr sb2)))
        (if (not (eq? (qa1 'read!) pra1))(display "agenda: unit-test 5 failing\n"))
        (if (not (eq? (qa2 'read!) pra2))(display "agenda: unit-test 6 failing\n"))
        (if (not (eq? (qb1 'read!) prb1))(display "agenda: unit-test 7 failing\n"))
        (if (not (eq? (qb2 'read!) prb2))(display "agenda: unit-test 8 failing\n"))
        (if (not (equal? (car sa1) 23))(display "agenda: unit-test 9 failing\n"))
        (if (not (equal? (car sa2) 7))(display "agenda: unit-test 10 failing\n"))
        (if (not (equal? (car sb1) 13))(display "agenda: unit-test 11 failing\n"))
        (if (not (equal? (car sb2) 5))(display "agenda: unit-test 12 failing\n"))
      )))
  ;; testing private method insert
  (let ((insert ((a 'debug) 'insert)))  ;; ignoring agenda b in this case
    (let ((L1 (insert 12 pra1 '())))    ;; using insert on empty list
      (if (not (equal? (length L1) 1)) (display "agenda: unit-test 13 failing\n"))
      (let ((T1 (caar L1)) (Q1 (cdar L1)))  ;; L1= ( (T1.Q1) )
        (if (not (equal? T1 12)) (display "agenda: unit-test 14 failing\n"))
        (if (not (eq?(Q1 'read!)pra1))(display "agenda: unit-test 15 failing\n"))))
    (let ((L2 (insert 7 pra2 (insert 14 pra1 '())))) ;; insertion 7 < 14
      (if (not (equal? (length L2) 2)) (display "agenda: unit-test 16 failing\n"))
      (let ((T1 (caadr L2)) (Q1 (cdadr L2)) (T2 (caar L2)) (Q2 (cdar L2)))
        (if (not (equal? T1 14)) (display "agenda: unit-test 17 failing\n"))
        (if (not (equal? T2 7)) (display "agenda: unit-test 18 failing\n"))
        (if (not (eq?(Q1 'read!)pra1))(display "agenda: unit-test 19 failing\n"))
        (if (not (eq?(Q2 'read!)pra2))(display "agenda: unit-test 20 failing\n"))))
    (let ((L2 (insert 13 pra2 (insert 4 pra1 '())))) ;; insertion 13 > 4
      (if (not (equal? (length L2) 2)) (display "agenda: unit-test 21 failing\n"))
      (let ((T1 (caadr L2)) (Q1 (cdadr L2)) (T2 (caar L2)) (Q2 (cdar L2)))
        (if (not (equal? T1 13)) (display "agenda: unit-test 22 failing\n"))
        (if (not (equal? T2 4)) (display "agenda: unit-test 23 failing\n"))
        (if (not (eq?(Q1 'read!)pra2))(display "agenda: unit-test 24 failing\n"))))
     (let ((L1 (insert 5 pra2 (insert 5 pra1 '())))) ;; insertion 5=5
      (if (not (equal? (length L1) 1)) (display "agenda: unit-test 25 failing\n"))
      (let ((T1 (caar L1)) (Q1 (cdar L1)))  ; only one time segment expected
        (if (not(equal? T1 5)) (display "agenda: unit-test 26 failing\n"))
        (if (not(eq?(Q1 'read!)pra1))(display "agenda: unit-test 27 failing\n"))
        (if (not(eq?(Q1 'read!)pra2))(display "agenda: unit-test 28 failing\n")))))
  ;; testing isempty?
  (begin ((a 'add-item!) 0 pra1) ((b 'add-item!) 0 prb1))
  (if (a 'isempty?) (display "agenda: unit-test 29 failing\n"))
  (if (b 'isempty?) (display "agenda: unit-test 30 failing\n"))
  (begin ((a 'add-item!) 0 pra2) ((b 'add-item!) 0 prb2))
  (if (a 'isempty?) (display "agenda: unit-test 31 failing\n"))
  (if (b 'isempty?) (display "agenda: unit-test 32 failing\n"))
  (begin (a 'read-next!) (b 'read-next!)) ; should still be non-empty after one read
  (if (a 'isempty?) (display "agenda: unit-test 33 failing\n"))
  (if (b 'isempty?) (display "agenda: unit-test 34 failing\n"))
  (begin (a 'read-next!) (b 'read-next!)) ; should be empty after second read-next
  (if (not (a 'isempty?)) (display "agenda: unit-test 35 failing\n"))
  (if (not (b 'isempty?)) (display "agenda: unit-test 36 failing\n"))
  ;; testing time again
  (if (not (zero? (a 'time))) (display "agenda: unit-test 37 failing\n"))
  (if (not (zero? (b 'time))) (display "agenda: unit-test 38 failing\n"))
  ;; testing add-item! and read-next
  (begin ((a 'add-item!) 1 pra1) ((a 'add-item!) 2 pra2) ((a 'add-item!) 3 pra3))
  (begin ((a 'add-item!) 1 pra2) ((a 'add-item!) 2 pra3) ((a 'add-item!) 3 pra4))
  (begin ((a 'add-item!) 1 pra3) ((a 'add-item!) 2 pra4) ((a 'add-item!) 3 pra1))
  (begin ((b 'add-item!) 4 prb1) ((b 'add-item!) 2 prb2) ((b 'add-item!) 5 prb3))
  (begin ((b 'add-item!) 4 prb2) ((b 'add-item!) 2 prb3) ((b 'add-item!) 5 prb4))
  (begin ((b 'add-item!) 4 prb3) ((b 'add-item!) 2 prb4) ((b 'add-item!) 5 prb1))
  ;;
  (let ((proc (a 'read-next!)))  ; checking succesive reads for a and current time
    (if (not (eq? proc pra1)) (display "agenda: unit-test 39 failing\n"))
    (if (not (equal? 1 (a 'time))) (display "agenda: unit-test 40 failing\n")))
  (let ((proc (a 'read-next!)))  ; #2
    (if (not (eq? proc pra2)) (display "agenda: unit-test 41 failing\n"))
    (if (not (equal? 1 (a 'time))) (display "agenda: unit-test 42 failing\n")))
  (let ((proc (a 'read-next!)))  ; #3
    (if (not (eq? proc pra3)) (display "agenda: unit-test 43 failing\n"))
    (if (not (equal? 1 (a 'time))) (display "agenda: unit-test 44 failing\n")))
  (let ((proc (a 'read-next!)))  ; #4
    (if (not (eq? proc pra2)) (display "agenda: unit-test 45 failing\n"))
    (if (not (equal? 2 (a 'time))) (display "agenda: unit-test 46 failing\n")))
  (let ((proc (a 'read-next!)))  ; #5
    (if (not (eq? proc pra3)) (display "agenda: unit-test 47 failing\n"))
    (if (not (equal? 2 (a 'time))) (display "agenda: unit-test 48 failing\n")))
  (let ((proc (a 'read-next!)))  ; #6
    (if (not (eq? proc pra4)) (display "agenda: unit-test 49 failing\n"))
    (if (not (equal? 2 (a 'time))) (display "agenda: unit-test 50 failing\n")))
  (let ((proc (a 'read-next!)))  ; #7
    (if (not (eq? proc pra3)) (display "agenda: unit-test 51 failing\n"))
    (if (not (equal? 3 (a 'time))) (display "agenda: unit-test 52 failing\n")))
  (let ((proc (a 'read-next!)))  ; #8
    (if (not (eq? proc pra4)) (display "agenda: unit-test 53 failing\n"))
    (if (not (equal? 3 (a 'time))) (display "agenda: unit-test 54 failing\n")))
  (let ((proc (a 'read-next!)))  ; #9
    (if (not (eq? proc pra1)) (display "agenda: unit-test 55 failing\n"))
    (if (not (equal? 3 (a 'time))) (display "agenda: unit-test 56 failing\n")))
  (if (not (a 'isempty?)) (display "agenda: unit-test 57 failing\n"))
  ;;
  (let ((proc (b 'read-next!)))  ; checking succesive reads for b and current time
    (if (not (eq? proc prb2)) (display "agenda: unit-test 58 failing\n"))
    (if (not (equal? 2 (b 'time))) (display "agenda: unit-test 59 failing\n")))
  (let ((proc (b 'read-next!)))  ; #2
    (if (not (eq? proc prb3)) (display "agenda: unit-test 60 failing\n"))
    (if (not (equal? 2 (b 'time))) (display "agenda: unit-test 61 failing\n")))
  (let ((proc (b 'read-next!)))  ; #3
    (if (not (eq? proc prb4)) (display "agenda: unit-test 62 failing\n"))
    (if (not (equal? 2 (b 'time))) (display "agenda: unit-test 63 failing\n")))
  (let ((proc (b 'read-next!)))  ; #4
    (if (not (eq? proc prb1)) (display "agenda: unit-test 64 failing\n"))
    (if (not (equal? 4 (b 'time))) (display "agenda: unit-test 65 failing\n")))
  (let ((proc (b 'read-next!)))  ; #5
    (if (not (eq? proc prb2)) (display "agenda: unit-test 66 failing\n"))
    (if (not (equal? 4 (b 'time))) (display "agenda: unit-test 67 failing\n")))
  (let ((proc (b 'read-next!)))  ; #6
    (if (not (eq? proc prb3)) (display "agenda: unit-test 68 failing\n"))
    (if (not (equal? 4 (b 'time))) (display "agenda: unit-test 69 failing\n")))
  (let ((proc (b 'read-next!)))  ; #7
    (if (not (eq? proc prb3)) (display "agenda: unit-test 70 failing\n"))
    (if (not (equal? 5 (b 'time))) (display "agenda: unit-test 71 failing\n")))
  (let ((proc (b 'read-next!)))  ; #8
    (if (not (eq? proc prb4)) (display "agenda: unit-test 72 failing\n"))
    (if (not (equal? 5 (b 'time))) (display "agenda: unit-test 73 failing\n")))
  (let ((proc (b 'read-next!)))  ; #9
    (if (not (eq? proc prb1)) (display "agenda: unit-test 74 failing\n"))
    (if (not (equal? 5 (b 'time))) (display "agenda: unit-test 75 failing\n")))
  (if (not (b 'isempty?)) (display "agenda: unit-test 76 failing\n"))
  ;; testing propagate
  (if (not (zero? count)) (display "agenda: unit-test 77 failing\n"))
  ;(define (pra1) (set! count (+ 1 (* 2 count))))
  ;(define (pra2) (set! count (+ 3 (* 5 count))))
  ;(define (pra3) (set! count (+ 7 (* 11 count))))
  ;(define (pra4) (set! count (+ 13 (* 17 count))))
  ;; first test: agenda a already at time 4
  (begin ((a 'add-item!) 5 pra4) ((a 'add-item!) 5 pra2) ((a 'add-item!) 4 pra3))
  (a 'propagate!)  ; pra3 > pra4 > pra2 > count = 663
  (if (not (equal? 663 count)) (display "agenda: unit-test 78 failing\n"))
  (if (not (a 'isempty?)) (display "agenda: unit-test 79 failing\n"))
  (if (not (equal? 5 (a 'time))) (display "agenda: unit-test 80 failing\n"))
  (set! count 0)
  ;; second test
  (begin ((a 'add-item!) 7 pra3) ((a 'add-item!) 6 pra1) ((a 'add-item!) 8 pra2))
  (a 'propagate!)  ; pra1 > pra3 > pra2 > count = 93
  (if (not (equal? 93 count)) (display "agenda: unit-test 81 failing\n"))
  (if (not (a 'isempty?)) (display "agenda: unit-test 82 failing\n"))
  (if (not (equal? 8 (a 'time))) (display "agenda: unit-test 83 failing\n"))
  (set! count 0)
  ;; testing reset
  (begin ((a 'add-item!) 8 pra1) ((a 'add-item!) 9 pra2) ((a 'add-item!) 10 pra3))
  (a 'propagate!)
  (begin ((a 'add-item!) 10 pra2)((a 'add-item!) 20 pra3)((a 'add-item!) 30 pra4))
  (a 'reset!)
  (if (not (a 'isempty?)) (display "agenda: unit-test 84 failing\n"))
  (if (not (equal? 0 (a 'time))) (display "agenda: unit-test 85 failing\n"))

  ;; exiting
  (display "agenda: unit test complete\n")
  'done)

(agenda-test)
(quit)
