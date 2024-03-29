(load "wire.scm")

(define (wire-test)
  ;; defining a few wires for testing
  (define a (wire))
  (define b (wire))
  (define c (wire))
  ;; gate-not
  (define in (wire))
  (define out (wire))
  ;; gate-or
  (define i1 (wire))
  (define i2 (wire))
  (define out1 (wire))
  ;; gate-and
  (define j1 (wire))
  (define j2 (wire))
  (define out2 (wire))
  ;; half-adder
  (define b1 (wire))
  (define b2 (wire))
  (define sum (wire))
  (define cry (wire))
  ;; full-adder
  (define k1 (wire))
  (define k2 (wire))
  (define cin (wire))
  (define s (wire))
  (define cout (wire))
  ;;
  (define count1 0)
  (define count2 0)
  (define count3 0)
  ;;
  (define (proc1) (set! count1 (+ count1 1)))
  (define (proc2) (set! count2 (+ count2 1)))
  (define (proc3) (set! count3 (+ count3 1)))
  ;; start
  (display "wire: starting unit test\n")
  (if (not (eq? #f (a 'get-signal))) (display "wire: unit test 1 failing\n"))
  (if (not (eq? #f (b 'get-signal))) (display "wire: unit test 2 failing\n"))
  (if (not (eq? #f (c 'get-signal))) (display "wire: unit test 3 failing\n"))
  ;;
  ((a 'set-signal!) #t)
  (if (not (eq? #t (a 'get-signal))) (display "wire: unit test 4 failing\n"))
  (if (not (eq? #f (b 'get-signal))) (display "wire: unit test 5 failing\n"))
  (if (not (eq? #f (c 'get-signal))) (display "wire: unit test 6 failing\n"))
  ;;
  ((b 'set-signal!) #t)
  (if (not (eq? #t (a 'get-signal))) (display "wire: unit test 7 failing\n"))
  (if (not (eq? #t (b 'get-signal))) (display "wire: unit test 8 failing\n"))
  (if (not (eq? #f (c 'get-signal))) (display "wire: unit test 9 failing\n"))
  ;;
  ((c 'set-signal!) #t)
  (if (not (eq? #t (a 'get-signal))) (display "wire: unit test 10 failing\n"))
  (if (not (eq? #t (b 'get-signal))) (display "wire: unit test 11 failing\n"))
  (if (not (eq? #t (c 'get-signal))) (display "wire: unit test 12 failing\n"))
   ;;
  ((a 'set-signal!) #f)
  ((b 'set-signal!) #f)
  ((c 'set-signal!) #f)
  (if (not (eq? #f (a 'get-signal))) (display "wire: unit test 13 failing\n"))
  (if (not (eq? #f (b 'get-signal))) (display "wire: unit test 14 failing\n"))
  (if (not (eq? #f (c 'get-signal))) (display "wire: unit test 15 failing\n"))
  ;;
  ;; adding proc1 proc2 and proc3 to a's action list
  ((a 'add-action!) proc1) ; proc1 should run ounce
  (if (not (= 1 count1)) (display "wire: unit test 16 failing\n"))
  ((a 'add-action!) proc2) ; proc2 should run ounce
  (if (not (= 1 count1)) (display "wire: unit test 17 failing\n"))
  (if (not (= 1 count2)) (display "wire: unit test 18 failing\n"))
  ((a 'add-action!) proc3) ; proc3 should run ounce
  (if (not (= 1 count1)) (display "wire: unit test 19 failing\n"))
  (if (not (= 1 count2)) (display "wire: unit test 20 failing\n"))
  (if (not (= 1 count3)) (display "wire: unit test 21 failing\n"))
  ;; adding proc2 and proc3 to b's action list
  ((b 'add-action!) proc2) ; proc2 should run ounce
  (if (not (= 1 count1)) (display "wire: unit test 22 failing\n"))
  (if (not (= 2 count2)) (display "wire: unit test 23 failing\n"))
  (if (not (= 1 count3)) (display "wire: unit test 24 failing\n"))
  ((b 'add-action!) proc3) ; proc3 should run ounce
  (if (not (= 1 count1)) (display "wire: unit test 25 failing\n"))
  (if (not (= 2 count2)) (display "wire: unit test 26 failing\n"))
  (if (not (= 2 count3)) (display "wire: unit test 27 failing\n"))
  ;; adding proc3 to c's action list
  ((c 'add-action!) proc3) ; proc3 should run ounce
  (if (not (= 1 count1)) (display "wire: unit test 28 failing\n"))
  (if (not (= 2 count2)) (display "wire: unit test 29 failing\n"))
  (if (not (= 3 count3)) (display "wire: unit test 30 failing\n"))
  ;;
  ;; trigerring acctions by signal change
  ((a 'set-signal!) #t) ; proc1, proc2 and proc3 should all run ounce
  (if (not (= 2 count1)) (display "wire: unit test 31 failing\n"))
  (if (not (= 3 count2)) (display "wire: unit test 32 failing\n"))
  (if (not (= 4 count3)) (display "wire: unit test 33 failing\n"))
  ((b 'set-signal!) #t) ; proc2 and proc3 should run ounce
  (if (not (= 2 count1)) (display "wire: unit test 34 failing\n"))
  (if (not (= 4 count2)) (display "wire: unit test 35 failing\n"))
  (if (not (= 5 count3)) (display "wire: unit test 36 failing\n"))
  ((c 'set-signal!) #t) ; proc3 should run ounce
  (if (not (= 2 count1)) (display "wire: unit test 37 failing\n"))
  (if (not (= 4 count2)) (display "wire: unit test 38 failing\n"))
  (if (not (= 6 count3)) (display "wire: unit test 39 failing\n"))
  ;; testing gate-not
  (if (not (eq? #f (in 'get-signal))) (display "wire: unit test 40 failing\n"))
  (if (not (eq? #f (out 'get-signal))) (display "wire: unit test 41 failing\n"))
  (gate-not in out)
  (schedule 'propagate!)
  (if (not (eq? #f (in 'get-signal))) (display "wire: unit test 42 failing\n"))
  (if (not (eq? #t (out 'get-signal))) (display "wire: unit test 43 failing\n"))
  ((in 'set-signal!) #t)  ; should change out
  (schedule 'propagate!)
  (if (not (eq? #t (in 'get-signal))) (display "wire: unit test 44 failing\n"))
  (if (not (eq? #f (out 'get-signal))) (display "wire: unit test 45 failing\n"))
  ((in 'set-signal!) #f)  ; should change out
  (schedule 'propagate!)
  (if (not (eq? #f (in 'get-signal))) (display "wire: unit test 46 failing\n"))
  (if (not (eq? #t (out 'get-signal))) (display "wire: unit test 47 failing\n"))
  ;; testing gate-or
  (if (not (eq? #f (i1 'get-signal))) (display "wire: unit test 48 failing\n"))
  (if (not (eq? #f (i2 'get-signal))) (display "wire: unit test 49 failing\n"))
  (if (not (eq? #f (out1 'get-signal))) (display "wire: unit test 50 failing\n"))
  (gate-or i1 i2 out1)
  (schedule 'propagate!)
  (if (not (eq? #f (i1 'get-signal))) (display "wire: unit test 51 failing\n"))
  (if (not (eq? #f (i2 'get-signal))) (display "wire: unit test 52 failing\n"))
  (if (not (eq? #f (out1 'get-signal))) (display "wire: unit test 53 failing\n"))
  ((i1 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #t (i1 'get-signal))) (display "wire: unit test 54 failing\n"))
  (if (not (eq? #f (i2 'get-signal))) (display "wire: unit test 55 failing\n"))
  (if (not (eq? #t (out1 'get-signal))) (display "wire: unit test 56 failing\n"))
  ((i1 'set-signal!) #f)
  ((i2 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #f (i1 'get-signal))) (display "wire: unit test 57 failing\n"))
  (if (not (eq? #t (i2 'get-signal))) (display "wire: unit test 58 failing\n"))
  (if (not (eq? #t (out1 'get-signal))) (display "wire: unit test 59 failing\n"))
  ((i1 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #t (i1 'get-signal))) (display "wire: unit test 60 failing\n"))
  (if (not (eq? #t (i2 'get-signal))) (display "wire: unit test 61 failing\n"))
  (if (not (eq? #t (out1 'get-signal))) (display "wire: unit test 62 failing\n"))
  ((i1 'set-signal!) #f)
  ((i2 'set-signal!) #f)
  (schedule 'propagate!)
  (if (not (eq? #f (i1 'get-signal))) (display "wire: unit test 63 failing\n"))
  (if (not (eq? #f (i2 'get-signal))) (display "wire: unit test 64 failing\n"))
  (if (not (eq? #f (out1 'get-signal))) (display "wire: unit test 65 failing\n"))
  ;; testing gate-and
  (if (not (eq? #f (j1 'get-signal))) (display "wire: unit test 66 failing\n"))
  (if (not (eq? #f (j2 'get-signal))) (display "wire: unit test 67 failing\n"))
  (if (not (eq? #f (out2 'get-signal))) (display "wire: unit test 68 failing\n"))
  (gate-and j1 j2 out2)
  (schedule 'propagate!)
  (if (not (eq? #f (j1 'get-signal))) (display "wire: unit test 69 failing\n"))
  (if (not (eq? #f (j2 'get-signal))) (display "wire: unit test 70 failing\n"))
  (if (not (eq? #f (out2 'get-signal))) (display "wire: unit test 71 failing\n"))
  ((j1 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #t (j1 'get-signal))) (display "wire: unit test 72 failing\n"))
  (if (not (eq? #f (j2 'get-signal))) (display "wire: unit test 73 failing\n"))
  (if (not (eq? #f (out2 'get-signal))) (display "wire: unit test 74 failing\n"))
  ((j1 'set-signal!) #f)
  ((j2 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #f (j1 'get-signal))) (display "wire: unit test 75 failing\n"))
  (if (not (eq? #t (j2 'get-signal))) (display "wire: unit test 76 failing\n"))
  (if (not (eq? #f (out2 'get-signal))) (display "wire: unit test 77 failing\n"))
  ((j1 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #t (j1 'get-signal))) (display "wire: unit test 78 failing\n"))
  (if (not (eq? #t (j2 'get-signal))) (display "wire: unit test 79 failing\n"))
  (if (not (eq? #t (out2 'get-signal))) (display "wire: unit test 80 failing\n"))
  ((j1 'set-signal!) #f)
  ((j2 'set-signal!) #f)
  (schedule 'propagate!)
  (if (not (eq? #f (j1 'get-signal))) (display "wire: unit test 81 failing\n"))
  (if (not (eq? #f (j2 'get-signal))) (display "wire: unit test 82 failing\n"))
  (if (not (eq? #f (out2 'get-signal))) (display "wire: unit test 83 failing\n"))
  ;; testing half-adder
  (if (not (eq? #f (b1 'get-signal))) (display "wire: unit test 84 failing\n"))
  (if (not (eq? #f (b2 'get-signal))) (display "wire: unit test 85 failing\n"))
  (if (not (eq? #f (sum 'get-signal))) (display "wire: unit test 86 failing\n"))
  (if (not (eq? #f (cry 'get-signal))) (display "wire: unit test 87 failing\n"))
  (half-adder b1 b2 sum cry)
  (schedule 'propagate!)
  (if (not (eq? #f (b1 'get-signal))) (display "wire: unit test 88 failing\n"))
  (if (not (eq? #f (b2 'get-signal))) (display "wire: unit test 89 failing\n"))
  (if (not (eq? #f (sum 'get-signal))) (display "wire: unit test 90 failing\n"))
  (if (not (eq? #f (cry 'get-signal))) (display "wire: unit test 91 failing\n"))
  ((b1 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #t (b1 'get-signal))) (display "wire: unit test 92 failing\n"))
  (if (not (eq? #f (b2 'get-signal))) (display "wire: unit test 93 failing\n"))
  (if (not (eq? #t (sum 'get-signal))) (display "wire: unit test 94 failing\n"))
  (if (not (eq? #f (cry 'get-signal))) (display "wire: unit test 95 failing\n"))
  ((b1 'set-signal!) #f)
  ((b2 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #f (b1 'get-signal))) (display "wire: unit test 96 failing\n"))
  (if (not (eq? #t (b2 'get-signal))) (display "wire: unit test 97 failing\n"))
  (if (not (eq? #t (sum 'get-signal))) (display "wire: unit test 98 failing\n"))
  (if (not (eq? #f (cry 'get-signal))) (display "wire: unit test 99 failing\n"))
  ((b1 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #t (b1 'get-signal))) (display "wire: unit test 100 failing\n"))
  (if (not (eq? #t (b2 'get-signal))) (display "wire: unit test 101 failing\n"))
  (if (not (eq? #f (sum 'get-signal))) (display "wire: unit test 102 failing\n"))
  (if (not (eq? #t (cry 'get-signal))) (display "wire: unit test 103 failing\n"))
  ((b1 'set-signal!) #f)
  ((b2 'set-signal!) #f)
  (schedule 'propagate!)
  (if (not (eq? #f (b1 'get-signal))) (display "wire: unit test 104 failing\n"))
  (if (not (eq? #f (b2 'get-signal))) (display "wire: unit test 105 failing\n"))
  (if (not (eq? #f (sum 'get-signal))) (display "wire: unit test 106 failing\n"))
  (if (not (eq? #f (cry 'get-signal))) (display "wire: unit test 107 failing\n"))
  ;;
  ;; testing full-adder
  (if (not (eq? #f (k1 'get-signal))) (display "wire: unit test 108 failing\n"))
  (if (not (eq? #f (k2 'get-signal))) (display "wire: unit test 109 failing\n"))
  (if (not (eq? #f (cin 'get-signal))) (display "wire: unit test 110 failing\n"))
  (if (not (eq? #f (s 'get-signal))) (display "wire: unit test 111 failing\n"))
  (if (not (eq? #f (cout 'get-signal))) (display "wire: unit test 112 failing\n"))
  (full-adder k1 k2 cin s cout)
  ;; (#t #f #f)
  ((k1 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #t (k1 'get-signal))) (display "wire: unit test 113 failing\n"))
  (if (not (eq? #f (k2 'get-signal))) (display "wire: unit test 114 failing\n"))
  (if (not (eq? #f (cin 'get-signal))) (display "wire: unit test 115 failing\n"))
  (if (not (eq? #t (s 'get-signal))) (display "wire: unit test 116 failing\n"))
  (if (not (eq? #f (cout 'get-signal))) (display "wire: unit test 117 failing\n"))
  ;; (#f #t #f)
  ((k1 'set-signal!) #f)
  ((k2 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #f (k1 'get-signal))) (display "wire: unit test 118 failing\n"))
  (if (not (eq? #t (k2 'get-signal))) (display "wire: unit test 119 failing\n"))
  (if (not (eq? #f (cin 'get-signal))) (display "wire: unit test 120 failing\n"))
  (if (not (eq? #t (s 'get-signal))) (display "wire: unit test 121 failing\n"))
  (if (not (eq? #f (cout 'get-signal))) (display "wire: unit test 122 failing\n"))
  ;; (#t #t #f)
  ((k1 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #t (k1 'get-signal))) (display "wire: unit test 123 failing\n"))
  (if (not (eq? #t (k2 'get-signal))) (display "wire: unit test 124 failing\n"))
  (if (not (eq? #f (cin 'get-signal))) (display "wire: unit test 125 failing\n"))
  (if (not (eq? #f (s 'get-signal))) (display "wire: unit test 126 failing\n"))
  (if (not (eq? #t (cout 'get-signal))) (display "wire: unit test 127 failing\n"))
  ;; (#f #f #t)
  ((k1 'set-signal!) #f)
  ((k2 'set-signal!) #f)
  ((cin 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #f (k1 'get-signal))) (display "wire: unit test 128 failing\n"))
  (if (not (eq? #f (k2 'get-signal))) (display "wire: unit test 129 failing\n"))
  (if (not (eq? #t (cin 'get-signal))) (display "wire: unit test 130 failing\n"))
  (if (not (eq? #t (s 'get-signal))) (display "wire: unit test 131 failing\n"))
  (if (not (eq? #f (cout 'get-signal))) (display "wire: unit test 132 failing\n"))
  ;; (#t #f #t)
  ((k1 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #t (k1 'get-signal))) (display "wire: unit test 133 failing\n"))
  (if (not (eq? #f (k2 'get-signal))) (display "wire: unit test 134 failing\n"))
  (if (not (eq? #t (cin 'get-signal))) (display "wire: unit test 135 failing\n"))
  (if (not (eq? #f (s 'get-signal))) (display "wire: unit test 136 failing\n"))
  (if (not (eq? #t (cout 'get-signal))) (display "wire: unit test 137 failing\n"))
  ;; (#f #t #t)
  ((k1 'set-signal!) #f)
  ((k2 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #f (k1 'get-signal))) (display "wire: unit test 138 failing\n"))
  (if (not (eq? #t (k2 'get-signal))) (display "wire: unit test 139 failing\n"))
  (if (not (eq? #t (cin 'get-signal))) (display "wire: unit test 140 failing\n"))
  (if (not (eq? #f (s 'get-signal))) (display "wire: unit test 141 failing\n"))
  (if (not (eq? #t (cout 'get-signal))) (display "wire: unit test 142 failing\n"))
  ;; (#t #t #t)
  ((k1 'set-signal!) #t)
  (schedule 'propagate!)
  (if (not (eq? #t (k1 'get-signal))) (display "wire: unit test 143 failing\n"))
  (if (not (eq? #t (k2 'get-signal))) (display "wire: unit test 144 failing\n"))
  (if (not (eq? #t (cin 'get-signal))) (display "wire: unit test 145 failing\n"))
  (if (not (eq? #t (s 'get-signal))) (display "wire: unit test 146 failing\n"))
  (if (not (eq? #t (cout 'get-signal))) (display "wire: unit test 147 failing\n"))
  ;; (#f #f #f)
  ((k1 'set-signal!) #f)
  ((k2 'set-signal!) #f)
  ((cin 'set-signal!) #f)
  (schedule 'propagate!)
  (if (not (eq? #f (k1 'get-signal))) (display "wire: unit test 148 failing\n"))
  (if (not (eq? #f (k2 'get-signal))) (display "wire: unit test 149 failing\n"))
  (if (not (eq? #f (cin 'get-signal))) (display "wire: unit test 150 failing\n"))
  (if (not (eq? #f (s 'get-signal))) (display "wire: unit test 151 failing\n"))
  (if (not (eq? #f (cout 'get-signal))) (display "wire: unit test 152 failing\n"))
  ;;
  (display "wire: unit test complete\n"))

(wire-test)
(exit 0)
