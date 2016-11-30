(load "transistor.scm")

(define (transistor-test)
 ;; start
  (display "transistor: starting unit test\n")
  ;;
  (global 'unit-test-true!)
  ;;
  (n-transistor-test)
  (p-transistor-test)
  ;; exiting
  (global 'time-reset!)
  (global 'unit-test-false!)
  ;;
  (display "transistor: unit test complete\n"))


(define (n-transistor-test)
  ;; defining wires for testing
  (define a (wire)) ; source or drain
  (define b (wire)) ; source or drain
  (define g (wire)) ; gate
  ;;
  (global 'error-count-reset!)
  ;; connecting wires
  (begin (n-transistor g a b) (global 'propagate!))
  ;; checking initial states
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 1 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 2 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 3 failing\n"))
  ;; a transitions
  ;; state 1
  ;; [a-> '()] from state [a = '() b = '() g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 4 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 5 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 6 failing\n"))
  ;; [a-> #f] from state [a = '() b = '() g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 7 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 8 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 9 failing\n"))
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 10 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 11 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 12 failing\n"))
  ;; [a-> #t] from state [a = '() b = '() g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 13 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 14 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 15 failing\n"))
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 16 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 17 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 18 failing\n"))
  ;; state 2
  ;; [a-> '()] from state [a = #f b = '() g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 19 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 20 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 21 failing\n"))
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 22 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 23 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 24 failing\n"))
  ;; [a-> #f] from state [a = #f b = '() g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 25 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 26 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 27 failing\n"))
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 28 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 29 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 30 failing\n"))
  ;; [a-> #t] from state [a = #f b = '() g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 31 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 32 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 33 failing\n"))
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 34 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 35 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 36 failing\n"))
  ;; state 3
  ;; [a-> '()] from state [a = #t b = '() g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 37 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 38 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 39 failing\n"))
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 40 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 41 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 42 failing\n"))
  ;; [a-> #f] from state [a = #t b = '() g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 43 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 44 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 45 failing\n"))
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 46 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 47 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 48 failing\n"))
  ;; [a-> #t] from state [a = #t b = '() g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 49 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 50 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 51 failing\n"))
  (begin ((a 'set-signal!) '() 'x)((b 'set-signal!) #f 'y) (global 'propagate!)) ; next
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 52 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 53 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 54 failing\n"))
  ;; state 4
  ;; [a-> '()] from state [a = '() b = #f g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 55 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 56 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 57 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 59 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 60 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 61 failing\n"))
  ;; [a-> #f] from state [a = '() b = #f g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 62 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 63 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 64 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 65 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 66 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 67 failing\n"))
  ;; [a-> #t] from state [a = '() b = #f g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 69 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 70 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 71 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 72 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 73 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 74 failing\n"))
  ;; state 5
  ;; [a-> '()] from state [a = #f b = #f g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 75 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 76 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 77 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 78 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 79 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 80 failing\n"))
  ;; [a-> #f] from state [a = #f b = #f g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 81 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 82 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 83 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 84 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 85 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 86 failing\n"))
  ;; [a-> #t] from state [a = #f b = #f g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 87 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 88 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 89 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 90 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 91 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 92 failing\n"))
  ;; state 6
  ;; [a-> '()] from state [a = #t b = #f g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 93 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 94 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 95 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 96 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 97 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 98 failing\n"))
  ;; [a-> #f] from state [a = #t b = #f g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 99 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 100 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 101 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 102 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 103 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 104 failing\n"))
  ;; [a-> #t] from state [a = #t b = #f g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 105 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 106 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 107 failing\n"))
  (begin ((a 'set-signal!) '() 'x)((b 'set-signal!) #t 'y)(global 'propagate!)) ; next
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 108 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 109 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 110 failing\n"))
  ;; state 7
  ;; [a-> '()] from state [a = '() b = #t g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 111 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 112 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 113 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 114 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 115 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 116 failing\n"))
  ;; [a-> #f] from state [a = '() b = #t g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 117 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 118 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 119 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 120 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 121 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 122 failing\n"))
  ;; [a-> #t] from state [a = '() b = #t g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 123 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 124 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 125 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 126 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 127 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 128 failing\n"))
  ;; state 8
  ;; [a-> '()] from state [a = #f b = #t g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 129 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 130 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 131 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 132 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 133 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 134 failing\n"))
  ;; [a-> #f] from state [a = #f b = #t g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 135 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 136 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 137 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 138 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 139 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 140 failing\n"))
  ;; [a-> #t] from state [a = #f b = #t g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 141 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 142 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 143 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 144 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 145 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 146 failing\n"))
  ;; state 9
  ;; [a-> '()] from state [a = #t b = #t g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 141 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 142 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 143 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 144 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 145 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 146 failing\n"))
  ;; [a-> #f] from state [a = #t b = #t g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 147 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 148 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 149 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 150 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 151 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 152 failing\n"))
  ;; [a-> #t] from state [a = #t b = #t g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 153 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 154 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 155 failing\n"))
  (begin ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) '() 'y)
         ((g 'set-signal!) #f  'z)
         (global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 155 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 156 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 157 failing\n"))
  ;; state 10
  ;; [a-> '()] from state [a = '() b = '() g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 158 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 159 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 160 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 161 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 162 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 163 failing\n"))
  ;; [a-> #f] from state [a = '() b = '() g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 164 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 165 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 166 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 167 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 168 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 169 failing\n"))
  ;; [a-> #t] from state [a = '() b = '() g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 170 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 171 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 172 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 173 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 174 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 175 failing\n"))
  ;; state 11
  ;; [a-> '()] from state [a = #f b = '() g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 176 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 177 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 178 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 179 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 180 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 181 failing\n"))
  ;; [a-> #f] from state [a = #f b = '() g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 182 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 183 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 184 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 185 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 186 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 187 failing\n"))
  ;; [a-> #t] from state [a = #f b = '() g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 188 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 189 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 190 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 191 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 192 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 193 failing\n"))
  ;; state 12
  ;; [a-> '()] from state [a = #t b = '() g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 194 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 195 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 196 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 197 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 198 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 199 failing\n"))
  ;; [a-> #f] from state [a = #t b = '() g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 200 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 201 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 202 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 203 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 204 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 205 failing\n"))
  ;; [a-> #t] from state [a = #t b = '() g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 206 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 207 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 208 failing\n"))
  (begin ((a 'set-signal!) '() 'x)((b 'set-signal!) #f 'y)(global 'propagate!)) ; next
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 209 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 210 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 211 failing\n"))
  ;; state 13
  ;; [a-> '()] from state [a = '() b = #f g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 212 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 213 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 214 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 215 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 216 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 217 failing\n"))
  ;; [a-> #f] from state [a = '() b = #f g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 218 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 219 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 220 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 221 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 222 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 223 failing\n"))
  ;; [a-> #t] from state [a = '() b = #f g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 224 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 225 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 226 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 227 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 228 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 229 failing\n"))
  ;; state 14
  ;; [a-> '()] from state [a = #f  b = #f g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 230 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 231 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 232 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 233 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 234 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 235 failing\n"))
  ;; [a-> #f] from state [a = #f  b = #f g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 236 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 237 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 238 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 239 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 240 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 241 failing\n"))
  ;; [a-> #t] from state [a = #f  b = #f g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 242 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 243 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 244 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 245 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 246 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 247 failing\n"))
  ;; state 15
  ;; [a-> '()] from state [a = #t  b = #f g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 248 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 249 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 250 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 251 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 252 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 253 failing\n"))
  ;; [a-> #f] from state [a = #t  b = #f g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 254 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 255 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 256 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 257 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 258 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 259 failing\n"))
  ;; [a-> #t] from state [a = #t  b = #f g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 260 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 261 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 262 failing\n"))
  (begin ((a 'set-signal!) '() 'x)((b 'set-signal!) #t 'y)(global 'propagate!)) ; next
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 263 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 264 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 265failing\n"))
  ;; state 16
  ;; [a-> '()] from state [a = '()  b = #t g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 266 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 267 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 268 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 269 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 270 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 271 failing\n"))
  ;; [a-> #f] from state [a = '()  b = #t g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 272 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 273 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 274 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 275 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 276 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 277 failing\n"))
  ;; [a-> #t] from state [a = '()  b = #t g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 278 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 279 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 280 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 281 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 282 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 283 failing\n"))
  ;; state 17
  ;; [a-> '()] from state [a = #f  b = #t g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 284 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 285 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 286 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 287 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 288 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 289 failing\n"))
  ;; [a-> #f] from state [a = #f  b = #t g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 290 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 291 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 292 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 293 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 294 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 295 failing\n"))
  ;; [a-> #t] from state [a = #f  b = #t g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 296 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 297 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 298 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 299 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 300 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 301 failing\n"))
  ;; state 18
  ;; [a-> '()] from state [a = #t  b = #t g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 302 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 303 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 304 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 305 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 306 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 307 failing\n"))
  ;; [a-> #f] from state [a = #t  b = #t g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 308 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 309 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 310 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 311 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 312 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 313 failing\n"))
  ;; [a-> #t] from state [a = #t  b = #t g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 314 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 315 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 316 failing\n"))
  (begin ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) '() 'y)
         ((g 'set-signal!) #t  'z)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 317 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 318 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 319 failing\n"))
  ;; state 19 (gate is now asserted)
  ;; [a-> '()] from state [a = '()  b = '() g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 320 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 321 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 322 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundnant)
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 323 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 324 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 325 failing\n"))
  ;; [a-> #f] from state [a = '()  b = '() g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; b should also be #f
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 326 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 327 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 328 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 329 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 330 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 331 failing\n"))
  ;; [a-> #t] from state [a = '()  b = '() g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; b should also be #t
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 332 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 333 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 334 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 335 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 336 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 337 failing\n"))
  ;; state 20 state [a = #f  b = '() g = #t ] cannot be reached
  ;; state 21 state [a = #t  b = '() g = #t ] cannot be reached
  ;; state 22 state [a = '()  b = #f g = #t ] cannot be reached
  ;; state 23
  ;; [a-> '()] from state [a = #f  b = #f g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!)) ; b should also be '()
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 338 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 339 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 340 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 341 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 342 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 343 failing\n"))
  ;; [a-> #f] from state [a = #f  b = #f g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; b should also be #f
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 344 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 345 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 346 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 347 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 348 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 349 failing\n"))
  ;; [a-> #t] from state [a = #f  b = #f g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; b should also be #t
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 350 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 351 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 352 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 353 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 354 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 355 failing\n"))
  ;; state 24 [a = #t  b = #f g = #t ] cannot be reached
  ;; state 25 [a = '() b = #t g = #t ] cannot be reached
  ;; state 26 [a = #f  b = #t g = #t ] cannot be reached
  ;; state 27
  ;; [a-> '()] from state [a = #t  b = #t g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!)) ; b should also be '()
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 356 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 357 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 358 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 359 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 360 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 361 failing\n"))
  ;; [a-> #f] from state [a = #t  b = #t g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; b should also be #f
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 362 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 363 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 364 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 365 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 366 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 367 failing\n"))
  ;; [a-> #t] from state [a = #t  b = #t g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; b should also be #t
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 368 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 369 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 370 failing\n"))
  (begin ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) '() 'y)
         ((g 'set-signal!) '() 'z)
         (global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 371 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 372 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 373 failing\n"))
  ;;
  ;; b transitions
  ;; state 1
  ;; [b-> '()] from state [b = '() a = '() g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 404 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 405 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 406 failing\n"))
  ;; [b-> #f] from state [b = '() a = '() g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 407 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 408 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 409 failing\n"))
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 410 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 411 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 412 failing\n"))
  ;; [b-> #t] from state [b = '() a = '() g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 413 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 414 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 415 failing\n"))
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 416 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 417 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 418 failing\n"))
  ;; state 2
  ;; [b-> '()] from state [b = #f a = '() g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 419 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 420 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 421 failing\n"))
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 422 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 423 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 424 failing\n"))
  ;; [b-> #f] from state [b = #f a = '() g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 425 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 426 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 427 failing\n"))
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 428 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 429 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 430 failing\n"))
  ;; [b-> #t] from state [b = #f a = '() g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 431 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 432 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 433 failing\n"))
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 434 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 435 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 436 failing\n"))
  ;; state 3
  ;; [b-> '()] from state [b = #t a = '() g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 437 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 438 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 439 failing\n"))
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 440 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 441 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 442 failing\n"))
  ;; [b-> #f] from state [b = #t a = '() g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 443 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 444 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 445 failing\n"))
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 446 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 447 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 448 failing\n"))
  ;; [b-> #t] from state [b = #t a = '() g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 449 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 450 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 451 failing\n"))
  (begin ((b 'set-signal!) '() 'y)((a 'set-signal!) #f 'x) (global 'propagate!)) ; next
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 452 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 453 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 454 failing\n"))
  ;; state 4
  ;; [b-> '()] from state [b = '() a = #f g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 455 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 456 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 457 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 459 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 460 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 461 failing\n"))
  ;; [b-> #f] from state [b = '() a = #f g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 462 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 463 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 464 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 465 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 466 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 467 failing\n"))
  ;; [b-> #t] from state [b = '() a = #f g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 469 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 470 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 471 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 472 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 473 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 474 failing\n"))
  ;; state 5
  ;; [b-> '()] from state [b = #f a = #f g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 475 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 476 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 477 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 478 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 479 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 480 failing\n"))
  ;; [b-> #f] from state [b = #f a = #f g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 481 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 482 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 483 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 484 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 485 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 486 failing\n"))
  ;; [b-> #t] from state [b = #f a = #f g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 487 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 488 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 489 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 490 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 491 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 492 failing\n"))
  ;; state 6
  ;; [b-> '()] from state [b = #t a = #f g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 493 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 494 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 495 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 496 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 497 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 498 failing\n"))
  ;; [b-> #f] from state [b = #t a = #f g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 499 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 500 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 501 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 502 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 503 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 504 failing\n"))
  ;; [b-> #t] from state [b = #t a = #f g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 505 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 506 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 507 failing\n"))
  (begin ((b 'set-signal!) '() 'y)((a 'set-signal!) #t 'x)(global 'propagate!)) ; next
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 508 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 509 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 510 failing\n"))
  ;; state 7
  ;; [b-> '()] from state [b = '() a = #t g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 511 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 512 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 513 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 514 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 515 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 516 failing\n"))
  ;; [b-> #f] from state [b = '() a = #t g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 517 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 518 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 519 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 520 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 521 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 522 failing\n"))
  ;; [b-> #t] from state [b = '() a = #t g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 523 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 524 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 525 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 526 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 527 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 528 failing\n"))
  ;; state 8
  ;; [b-> '()] from state [b = #f a = #t g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 529 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 530 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 531 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 532 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 533 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 534 failing\n"))
  ;; [b-> #f] from state [b = #f a = #t g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 535 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 536 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 537 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 538 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 539 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 540 failing\n"))
  ;; [b-> #t] from state [b = #f a = #t g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 541 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 542 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 543 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 544 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 545 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 546 failing\n"))
  ;; state 9
  ;; [b-> '()] from state [b = #t a = #t g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 541 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 542 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 543 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 544 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 545 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 546 failing\n"))
  ;; [b-> #f] from state [b = #t a = #t g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 547 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 548 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 549 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 550 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 551 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 552 failing\n"))
  ;; [b-> #t] from state [b = #t a = #t g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 553 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 554 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 555 failing\n"))
  (begin ((b 'set-signal!) '() 'y)
         ((a 'set-signal!) '() 'x)
         ((g 'set-signal!) #f  'z)
         (global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 555 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 556 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 557 failing\n"))
  ;; state 10
  ;; [b-> '()] from state [b = '() a = '() g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 558 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 559 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 560 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 561 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 562 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 563 failing\n"))
  ;; [b-> #f] from state [b = '() a = '() g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 564 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 565 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 566 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 567 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 568 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 569 failing\n"))
  ;; [b-> #t] from state [b = '() a = '() g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 570 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 571 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 572 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 573 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 574 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 575 failing\n"))
  ;; state 11
  ;; [b-> '()] from state [b = #f a = '() g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 576 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 577 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 578 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 579 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 580 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 581 failing\n"))
  ;; [b-> #f] from state [b = #f a = '() g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 582 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 583 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 584 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 585 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 586 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 587 failing\n"))
  ;; [b-> #t] from state [b = #f a = '() g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 588 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 589 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 590 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 591 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 592 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 593 failing\n"))
  ;; state 12
  ;; [b-> '()] from state [b = #t a = '() g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 594 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 595 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 596 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 597 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 598 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 599 failing\n"))
  ;; [b-> #f] from state [b = #t a = '() g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 600 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 601 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 602 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 603 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 604 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 605 failing\n"))
  ;; [b-> #t] from state [b = #t a = '() g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 606 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 607 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 608 failing\n"))
  (begin ((b 'set-signal!) '() 'y)((a 'set-signal!) #f 'x)(global 'propagate!)) ; next
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 609 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 610 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 611 failing\n"))
  ;; state 13
  ;; [b-> '()] from state [b = '() a = #f g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 612 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 613 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 614 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 615 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 616 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 617 failing\n"))
  ;; [b-> #f] from state [b = '() a = #f g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 618 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 619 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 620 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 621 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 622 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 623 failing\n"))
  ;; [b-> #t] from state [b = '() a = #f g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 624 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 625 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 626 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 627 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 628 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 629 failing\n"))
  ;; state 14
  ;; [b-> '()] from state [b = #f  a = #f g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 630 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 631 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 632 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 633 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 634 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 635 failing\n"))
  ;; [b-> #f] from state [b = #f  a = #f g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 636 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 637 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 638 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 639 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 640 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 641 failing\n"))
  ;; [b-> #t] from state [b = #f  a = #f g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 642 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 643 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 644 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 645 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 646 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 647 failing\n"))
  ;; state 15
  ;; [b-> '()] from state [b = #t  a = #f g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 648 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 649 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 650 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 651 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 652 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 653 failing\n"))
  ;; [b-> #f] from state [b = #t  a = #f g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 654 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 655 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 656 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 657 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 658 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 659 failing\n"))
  ;; [b-> #t] from state [b = #t  a = #f g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 660 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 661 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 662 failing\n"))
  (begin ((b 'set-signal!) '() 'y)((a 'set-signal!) #t 'x)(global 'propagate!)) ; next
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 663 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 664 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 665 failing\n"))
  ;; state 16
  ;; [b-> '()] from state [b = '()  a = #t g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 666 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 667 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 668 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 669 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 670 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 671 failing\n"))
  ;; [b-> #f] from state [b = '()  a = #t g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 672 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 673 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 674 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 675 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 676 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 677 failing\n"))
  ;; [b-> #t] from state [b = '()  a = #t g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 678 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 679 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 680 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 681 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 682 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 683 failing\n"))
  ;; state 17
  ;; [b-> '()] from state [b = #f  a = #t g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 684 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 685 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 686 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 687 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 688 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 689 failing\n"))
  ;; [b-> #f] from state [b = #f  a = #t g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 690 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 691 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 692 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 693 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 694 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 695 failing\n"))
  ;; [b-> #t] from state [b = #f  a = #t g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 696 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 697 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 698 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 699 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 700 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 701 failing\n"))
  ;; state 18
  ;; [b-> '()] from state [b = #t  a = #t g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 702 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 703 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 704 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 705 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 706 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 707 failing\n"))
  ;; [b-> #f] from state [b = #t  a = #t g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 708 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 709 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 710 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 711 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 712 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 713 failing\n"))
  ;; [b-> #t] from state [b = #t  a = #t g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 714 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 715 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 716 failing\n"))
  (begin ((b 'set-signal!) '() 'y)
         ((a 'set-signal!) '() 'x)
         ((g 'set-signal!) #t  'z)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 717 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 718 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 719 failing\n"))
  ;; state 19 (gate is now asserted)
  ;; [b-> '()] from state [b = '()  a = '() g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 720 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 721 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 722 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state (redundnant)
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 723 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 724 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 725 failing\n"))
  ;; [b-> #f] from state [b = '()  a = '() g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; a should also be #f
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 726 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 727 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 728 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 729 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 730 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 731 failing\n"))
  ;; [b-> #t] from state [b = '()  a = '() g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; a should also be #t
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 732 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 733 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 734 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 735 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 736 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 737 failing\n"))
  ;; state 20 state [b = #f  a = '() g = #t ] cannot be reached
  ;; state 21 state [b = #t  a = '() g = #t ] cannot be reached
  ;; state 22 state [b = '()  a = #f g = #t ] cannot be reached
  ;; state 23
  ;; [b-> '()] from state [b = #f  a = #f g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!)) ; a should also be '()
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 738 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 739 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 740 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 741 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 742 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 743 failing\n"))
  ;; [b-> #f] from state [b = #f  a = #f g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; a should also be #f
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 744 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 745 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 746 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 747 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 748 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 749 failing\n"))
  ;; [b-> #t] from state [b = #f  a = #f g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; a should also be #t
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 750 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 751 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 752 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 753 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 754 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 755 failing\n"))
  ;; state 24 [b = #t  a = #f g = #t ] cannot be reached
  ;; state 25 [b = '() a = #t g = #t ] cannot be reached
  ;; state 26 [b = #f  a = #t g = #t ] cannot be reached
  ;; state 27
  ;; [b-> '()] from state [b = #t  a = #t g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!)) ; a should also be '()
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 756 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 757 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 758 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 759 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 760 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 761 failing\n"))
  ;; [b-> #f] from state [b = #t  a = #t g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; a should also be #f
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 762 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 763 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 764 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 765 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 766 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 767 failing\n"))
  ;; [b-> #t] from state [b = #t  a = #t g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; a should also be #t
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 768 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 769 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 770 failing\n"))
  (begin ((b 'set-signal!) '() 'y)
         ((a 'set-signal!) '() 'x)
         ((g 'set-signal!) '() 'z)
         (global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 771 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 772 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 773 failing\n"))
  ;;
  ;; g transitions
  ;; state 1
  ;; [g-> '()] from state [g = '() a = '() b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 804 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 805 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 806 failing\n"))
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 807 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 808 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 809 failing\n"))
  ;; [g-> #f] from state [g = '() a = '() b = '()]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 810 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 811 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 812 failing\n"))
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 813 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 814 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 815 failing\n"))
  ;; [g-> #t] from state [g = '() a = '() b = '()]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 816 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 817 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 818 failing\n"))
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 819 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 820 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 821 failing\n"))
  ;; state 2
  ;; [g-> '()] from state [g = #f a = '() b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 822 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 823 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 824 failing\n"))
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 825 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 826 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 827 failing\n"))
  ;; [g-> #f] from state [g = #f a = '() b = '()]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 828 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 829 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 830 failing\n"))
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 831 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 832 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 833 failing\n"))
  ;; [g-> #t] from state [g = #f a = '() b = '()]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 834 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 835 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 836 failing\n"))
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 837 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 838 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 839 failing\n"))
  ;; state 3
  ;; [g-> '()] from state [g = #t a = '() b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 840 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 841 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 842 failing\n"))
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 843 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 844 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 845 failing\n"))
  ;; [g-> #f] from state [g = #t a = '() b = '()]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 846 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 847 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 848 failing\n"))
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 849 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 850 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 851 failing\n"))
  ;; [g-> #t] from state [g = #t a = '() b = '()]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 852 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 853 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 854 failing\n"))
  (begin ((g 'set-signal!) '() 'z)((a 'set-signal!) #f 'x)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 855 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 856 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 857 failing\n"))
  ;; state 4
  ;; [g-> '()] from state [g = '() a = #f b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 858 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 859 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 860 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; setting next state (redundnant)
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 861 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 862 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 863 failing\n"))
  ;; [g-> #f] from state [g = '() a = #f b = '()]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 864 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 865 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 866 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 867 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 868 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 869 failing\n"))
  ;; [g-> #t] from state [g = '() a = #f b = '()] (b should be #f)
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 870 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 871 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 872 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 873 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 874 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 875 failing\n"))
  ;; state 5
  ;; [g-> '()] from state [g = #f a = #f b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 876 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 877 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 878 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 879 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 880 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 881 failing\n"))
  ;; [g-> #f] from state [g = #f a = #f b = '()]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 882 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 883 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 884 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 885 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 886 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 887 failing\n"))
  ;; [g-> #t] from state [g = #f a = #f b = '()] (b should be #f)
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 888 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 889 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 890 failing\n"))
  (begin ((g 'set-signal!) '() 'z)((a 'set-signal!) #t 'x)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 891 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 892 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 893 failing\n"))
  ;; state 6 state [g = #t a = #f b = '()] cannot be reached
  ;; state 7
  ;; [g-> '()] from state [g = '() a = #t b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 894 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 895 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 896 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 897 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 898 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 899 failing\n"))
  ;; [g-> #f] from state [g = '() a = #t b = '()]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 900 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 901 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 902 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 903 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 904 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 905 failing\n"))
  ;; [g-> #t] from state [g = '() a = #t b = '()] (b should be #t)
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 906 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 907 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 908 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 909 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 910 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 911 failing\n"))
  ;; state 8
  ;; [g-> '()] from state [g = #f a = #t b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 912 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 913 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 914 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 915 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 916 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 917 failing\n"))
  ;; [g-> #f] from state [g = #f a = #t b = '()]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 918 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 919 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 920 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 921 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 922 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display "transistor: unit-test 923 failing\n"))
  ;; [g-> #t] from state [g = #f a = #t b = '()] (b should be #t)
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 924 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display "transistor: unit-test 925 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display "transistor: unit-test 926 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!) ; one more propagate
         ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) #f  'y)(global 'propagate!))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 927 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 928 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 929 failing\n"))
  ;; state 9 state [g = #t a = #t b = '()] cannot be reached
  ;; state 10
  ;; [g-> '()] from state [g = '() a = '() b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 930 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 931 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 932 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 933 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 934 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 935 failing\n"))
  ;; [g-> #f] from state [g = '() a = '() b = #f]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 936 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 937 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 938 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 939 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 940 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 941 failing\n"))
  ;; [g-> #t] from state [g = '() a = '() b = #f] (a should be #f)
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 942 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 943 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 944 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 945 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 946 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 947 failing\n"))
  ;; state 11
  ;; [g-> '()] from state [g = #f a = '() b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 948 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 949 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 950 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 951 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 952 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 953 failing\n"))
  ;; [g-> #f] from state [g = #f a = '() b = #f]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 954 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 955 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 956 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next (redundant)
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 957 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display "transistor: unit-test 958 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 959 failing\n"))
  ;; [g-> #t] from state [g = #f a = '() b = #f] (a should be #f)
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 960 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 961 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 962 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!) ; one more propagate
         ((a 'set-signal!) #f 'x)(global 'propagate!))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 963 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 964 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 965 failing\n"))
  ;; state 12 state [g = #t a = '() b = #f] cannot be reached
  ;; state 13
  ;; [g-> '()] from state [g = '() a = #f b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 966 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 967 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 968 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next (redundant)
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 969 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 970 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 971 failing\n"))
  ;; [g-> #f] from state [g = '() a = #f b = #f]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 972 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 973 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 974 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 975 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 976 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 977 failing\n"))
  ;; [g-> #t] from state [g = '() a = #f b = #f]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 978 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 979 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 980 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 981 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 982 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 983 failing\n"))
  ;; state 14
  ;; [g-> '()] from state [g = #f a = #f b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display "transistor: unit-test 984 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 985 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 986 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 987 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 988 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 989 failing\n"))
  ;; [g-> #f] from state [g = #f a = #f b = #f]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 990 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 991 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 992 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next (redundant)
  (if(not(eq? #f (g 'get-signal)))(display "transistor: unit-test 993 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 994 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 995 failing\n"))
  ;; [g-> #t] from state [g = #f a = #f b = #f]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 996 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display "transistor: unit-test 997 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display "transistor: unit-test 998 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display "transistor: unit-test 999 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1000 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1001 failing\n"))
  ;; state 15
  ;; [g-> '()] from state [g = #t a = #f b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1002 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1003 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1004 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1005 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1006 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1007 failing\n"))
  ;; [g-> #f] from state [g = #t a = #f b = #f]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1009 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1010 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1011 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1012 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1013 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1014 failing\n"))
  ;; [g-> #t] from state [g = #t a = #f b = #f]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1015 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1016 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1017 failing\n"))
  (begin ((g 'set-signal!) '() 'z)((a 'set-signal!) #t 'x)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1018 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1019 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1020 failing\n"))
  ;; state 16
  ;; [g-> '()] from state [g = '() a = #t b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1021 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1022 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1023 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1024 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1025 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1026 failing\n"))
  ;; [g-> #f] from state [g = '() a = #t b = #f]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1027 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1028 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1029 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1030 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1031 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1032 failing\n"))
  ;; [g-> #t] from state [g = '() a = #t b = #f] (short circuit)
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(= 0(global 'error-count)))(display"transistor:unit-test 1033 failing\n"))
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(= 2(global 'error-count)))(display"transistor:unit-test 1034 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1035 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1036 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1037 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1038 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1039 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1040 failing\n"))
  ;; state 17
  ;; [g-> '()] from state [g = #f a = #t b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1041 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1042 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1043 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1044 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1045 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1046 failing\n"))
  ;; [g-> #f] from state [g = #f a = #t b = #f]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1047 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1048 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1049 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1050 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1051 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1052 failing\n"))
  ;; [g-> #t] from state [g = #f a = #t b = #f]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(= 2(global 'error-count)))(display"transistor:unit-test 1053 failing\n"))
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(= 4(global 'error-count)))(display"transistor:unit-test 1054 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1055 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1056 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 1057 failing\n"))
  (begin ((g 'set-signal!) '() 'z)
         ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) #t  'y)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1058 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1059 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1060 failing\n"))
  ;; state 18 state [g = #t a = #t b = #f] cannot be reached
  ;; well in fact this state can be reached which is a flaw
  ;; propagate! will generate 2 error messages. However subsequent propagate!
  ;; will provide no further warning and state [g = #t a = #t b = #f]
  ;; will be maintained despite being inconsistent.
  ;; state 19
  ;; [g-> '()] from state [g = '() a = '() b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1061 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1062 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1063 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1064 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1065 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1066 failing\n"))
  ;; [g-> #f] from state [g = '() a = '() b = #t]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1067 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1068 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1069 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1070 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1071 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1072 failing\n"))
  ;; [g-> #t] from state [g = '() a = '() b = #t] (a should be #t)
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1073 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1074 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1075 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1076 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1077 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1078 failing\n"))
  ;; state 20
  ;; [g-> '()] from state [g = #f a = '() b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1079 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1080 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1081 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1082 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1083 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1084 failing\n"))
  ;; [g-> #f] from state [g = #f a = '() b = #t]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1085 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1086 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1087 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1088 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1089 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1090 failing\n"))
  ;; [g-> #t] from state [g = #f a = '() b = #t] (a should be #t)
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1091 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1092 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1093 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)  ; one more propagate!
         ((a 'set-signal!) #f 'x) (global 'propagate!))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1094 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1095 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1096 failing\n"))
  ;; state 21 state [g = #t a = '() b = #t] cannot be reached
  ;; state 22
  ;; [g-> '()] from state [g = '() a = #f b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1097 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1098 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1099 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1100 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1101 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1102 failing\n"))
  ;; [g-> #f] from state [g = '() a = #f b = #t]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1103 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1104 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1105 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1106 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1107 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1108 failing\n"))
  ;; [g-> #t] from state [g = '() a = #f b = #t]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(= 4(global 'error-count)))(display"transistor:unit-test 1109 failing\n"))
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(= 6(global 'error-count)))(display"transistor:unit-test 1111 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1112 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1113 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1114 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1115 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1116 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1117 failing\n"))
  ;; state 23
  ;; [g-> '()] from state [g = #f a = #f b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1118 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1119 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1120 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1121 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1122 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1123 failing\n"))
  ;; [g-> #f] from state [g = #f a = #f b = #t]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1124 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1125 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1126 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1127 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1128 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1129 failing\n"))
  ;; [g-> #t] from state [g = #f a = #f b = #t]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(= 6(global 'error-count)))(display"transistor:unit-test 1130 failing\n"))
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(= 8(global 'error-count)))(display"transistor:unit-test 1131 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1132 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 1133 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1134 failing\n"))
  (begin ((g 'set-signal!)'() 'z)((a 'set-signal!) #t 'x) (global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1135 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1136 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1137 failing\n"))
  ;; state 24 state [g = #t a = #f b = #t] cannot be reached
  ;; well in fact this state can be reached which is a flaw
  ;; propagate! will generate 2 error messages. However subsequent propagate!
  ;; will provide no further warning and state [g = #t a = #t b = #f]
  ;; will be maintained despite being inconsistent.
  ;; state 25
  ;; [g-> '()] from state [g = '() a = #t b = #t]
  (begin ((g 'set-signal!) '()'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1138 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1139 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1140 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1141 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1142 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1143 failing\n"))
  ;; [g-> #f] from state [g = '() a = #t b = #t]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1144 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1145 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1146 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1147 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1148 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1149 failing\n"))
  ;; [g-> #t] from state [g = '() a = #t b = #t]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1150 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1151 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1152 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1153 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1154 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1155 failing\n"))
  ;; state 26
  ;; [g-> '()] from state [g = #f a = #t b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1156 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1157 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1158 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1159 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1160 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1161 failing\n"))
  ;; [g-> #f] from state [g = #f a = #t b = #t]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1162 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1163 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1164 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1165 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1166 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1167 failing\n"))
  ;; [g-> #t] from state [g = #f a = #t b = #t]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1169 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1170 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1171 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1172 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1173 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1174 failing\n"))
  ;; state 27
  ;; [g-> '()] from state [g = #t a = #t b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1175 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1176 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1177 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1178 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1179 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1180 failing\n"))
  ;; [g-> #f] from state [g = #t a = #t b = #t]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 1181 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1182 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1183 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1184 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1185 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1186 failing\n"))
  ;; [g-> #t] from state [g = #t a = #t b = #t]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 1187 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 1188 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 1189 failing\n"))
  (begin ((g 'set-signal!) '() 'z)
         ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) '() 'y)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 1190 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 1191 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 1192 failing\n"))
  )


;; code produced from n-transistor::unit-test by switching #f and #t
;; while connecting g a b to a p-transistor instead of n-transistor.
;; error codes have also been changed.
(define (p-transistor-test)
  ;; defining wires for testing
  (define a (wire)) ; source or drain
  (define b (wire)) ; source or drain
  (define g (wire)) ; gate
  ;;
  (global 'error-count-reset!)
  ;; connecting wires
  (begin (p-transistor g a b) (global 'propagate!))
  ;; checking initial states
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2001 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2002 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2003 failing\n"))
  ;; a transitions
  ;; state 1
  ;; [a-> '()] from state [a = '() b = '() g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2004 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2005 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2006 failing\n"))
  ;; [a-> #t] from state [a = '() b = '() g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2007 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2008 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2009 failing\n"))
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2010 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2011 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2012 failing\n"))
  ;; [a-> #f] from state [a = '() b = '() g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2013 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2014 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2015 failing\n"))
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2016 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2017 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2018 failing\n"))
  ;; state 2
  ;; [a-> '()] from state [a = #t b = '() g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2019 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2020 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2021 failing\n"))
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2022 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2023 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2024 failing\n"))
  ;; [a-> #t] from state [a = #t b = '() g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2025 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2026 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2027 failing\n"))
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2028 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2029 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2030 failing\n"))
  ;; [a-> #f] from state [a = #t b = '() g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2031 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2032 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2033 failing\n"))
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2034 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2035 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2036 failing\n"))
  ;; state 3
  ;; [a-> '()] from state [a = #f b = '() g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2037 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2038 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2039 failing\n"))
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2040 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2041 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2042 failing\n"))
  ;; [a-> #t] from state [a = #f b = '() g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2043 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2044 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2045 failing\n"))
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2046 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2047 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2048 failing\n"))
  ;; [a-> #f] from state [a = #f b = '() g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2049 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2050 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2051 failing\n"))
  (begin ((a 'set-signal!) '() 'x)((b 'set-signal!) #t 'y) (global 'propagate!)) ; next
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2052 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2053 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2054 failing\n"))
  ;; state 4
  ;; [a-> '()] from state [a = '() b = #t g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2055 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2056 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2057 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2059 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2060 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2061 failing\n"))
  ;; [a-> #t] from state [a = '() b = #t g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2062 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2063 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2064 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2065 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2066 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2067 failing\n"))
  ;; [a-> #f] from state [a = '() b = #t g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2069 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2070 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2071 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2072 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2073 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2074 failing\n"))
  ;; state 5
  ;; [a-> '()] from state [a = #t b = #t g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2075 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2076 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2077 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2078 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2079 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2080 failing\n"))
  ;; [a-> #t] from state [a = #t b = #t g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2081 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2082 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2083 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2084 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2085 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2086 failing\n"))
  ;; [a-> #f] from state [a = #t b = #t g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2087 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2088 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2089 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2090 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2091 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2092 failing\n"))
  ;; state 6
  ;; [a-> '()] from state [a = #f b = #t g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2093 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2094 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2095 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2096 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2097 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2098 failing\n"))
  ;; [a-> #t] from state [a = #f b = #t g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2099 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2100 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2101 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2102 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2103 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2104 failing\n"))
  ;; [a-> #f] from state [a = #f b = #t g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2105 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2106 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2107 failing\n"))
  (begin ((a 'set-signal!) '() 'x)((b 'set-signal!) #f 'y)(global 'propagate!)) ; next
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2108 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2109 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2110 failing\n"))
  ;; state 7
  ;; [a-> '()] from state [a = '() b = #f g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2111 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2112 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2113 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2114 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2115 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2116 failing\n"))
  ;; [a-> #t] from state [a = '() b = #f g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2117 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2118 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2119 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2120 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2121 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2122 failing\n"))
  ;; [a-> #f] from state [a = '() b = #f g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2123 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2124 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2125 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2126 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2127 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2128 failing\n"))
  ;; state 8
  ;; [a-> '()] from state [a = #t b = #f g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2129 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2130 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2131 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2132 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2133 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2134 failing\n"))
  ;; [a-> #t] from state [a = #t b = #f g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2135 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2136 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2137 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2138 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2139 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2140 failing\n"))
  ;; [a-> #f] from state [a = #t b = #f g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2141 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2142 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2143 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2144 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2145 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2146 failing\n"))
  ;; state 9
  ;; [a-> '()] from state [a = #f b = #f g = '()]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2141 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2142 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2143 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2144 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2145 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2146 failing\n"))
  ;; [a-> #t] from state [a = #f b = #f g = '()]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2147 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2148 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2149 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2150 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2151 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2152 failing\n"))
  ;; [a-> #f] from state [a = #f b = #f g = '()]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2153 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2154 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2155 failing\n"))
  (begin ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) '() 'y)
         ((g 'set-signal!) #t  'z)
         (global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2155 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2156 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2157 failing\n"))
  ;; state 10
  ;; [a-> '()] from state [a = '() b = '() g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2158 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2159 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2160 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2161 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2162 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2163 failing\n"))
  ;; [a-> #t] from state [a = '() b = '() g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2164 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2165 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2166 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2167 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2168 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2169 failing\n"))
  ;; [a-> #f] from state [a = '() b = '() g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2170 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2171 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2172 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2173 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2174 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2175 failing\n"))
  ;; state 11
  ;; [a-> '()] from state [a = #t b = '() g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2176 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2177 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2178 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2179 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2180 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2181 failing\n"))
  ;; [a-> #t] from state [a = #t b = '() g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2182 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2183 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2184 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2185 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2186 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2187 failing\n"))
  ;; [a-> #f] from state [a = #t b = '() g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2188 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2189 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2190 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2191 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2192 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2193 failing\n"))
  ;; state 12
  ;; [a-> '()] from state [a = #f b = '() g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2194 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2195 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2196 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2197 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2198 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2199 failing\n"))
  ;; [a-> #t] from state [a = #f b = '() g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2200 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2201 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2202 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2203 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2204 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2205 failing\n"))
  ;; [a-> #f] from state [a = #f b = '() g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2206 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2207 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2208 failing\n"))
  (begin ((a 'set-signal!) '() 'x)((b 'set-signal!) #t 'y)(global 'propagate!)) ; next
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2209 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2210 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2211 failing\n"))
  ;; state 13
  ;; [a-> '()] from state [a = '() b = #t g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2212 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2213 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2214 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2215 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2216 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2217 failing\n"))
  ;; [a-> #t] from state [a = '() b = #t g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2218 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2219 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2220 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2221 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2222 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2223 failing\n"))
  ;; [a-> #f] from state [a = '() b = #t g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2224 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2225 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2226 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2227 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2228 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2229 failing\n"))
  ;; state 14
  ;; [a-> '()] from state [a = #t  b = #t g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2230 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2231 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2232 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2233 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2234 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2235 failing\n"))
  ;; [a-> #t] from state [a = #t  b = #t g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2236 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2237 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2238 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2239 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2240 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2241 failing\n"))
  ;; [a-> #f] from state [a = #t  b = #t g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2242 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2243 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2244 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2245 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2246 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2247 failing\n"))
  ;; state 15
  ;; [a-> '()] from state [a = #f  b = #t g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2248 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2249 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2250 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2251 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2252 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2253 failing\n"))
  ;; [a-> #t] from state [a = #f  b = #t g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2254 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2255 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2256 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2257 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2258 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2259 failing\n"))
  ;; [a-> #f] from state [a = #f  b = #t g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2260 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2261 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2262 failing\n"))
  (begin ((a 'set-signal!) '() 'x)((b 'set-signal!) #f 'y)(global 'propagate!)) ; next
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2263 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2264 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2265 failing\n"))
  ;; state 16
  ;; [a-> '()] from state [a = '()  b = #f g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2266 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2267 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2268 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2269 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2270 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2271 failing\n"))
  ;; [a-> #t] from state [a = '()  b = #f g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2272 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2273 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2274 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2275 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2276 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2277 failing\n"))
  ;; [a-> #f] from state [a = '()  b = #f g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2278 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2279 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2280 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2281 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2282 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2283 failing\n"))
  ;; state 17
  ;; [a-> '()] from state [a = #t  b = #f g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2284 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2285 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2286 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2287 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2288 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2289 failing\n"))
  ;; [a-> #t] from state [a = #t  b = #f g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2290 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2291 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2292 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2293 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2294 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2295 failing\n"))
  ;; [a-> #f] from state [a = #t  b = #f g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2296 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2297 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2298 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2299 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2300 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2301 failing\n"))
  ;; state 18
  ;; [a-> '()] from state [a = #f  b = #f g = #t ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2302 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2303 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2304 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2305 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2306 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2307 failing\n"))
  ;; [a-> #t] from state [a = #f  b = #f g = #t ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2308 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2309 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2310 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2311 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2312 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2313 failing\n"))
  ;; [a-> #f] from state [a = #f  b = #f g = #t ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2314 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2315 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2316 failing\n"))
  (begin ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) '() 'y)
         ((g 'set-signal!) #f  'z)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2317 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2318 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2319 failing\n"))
  ;; state 19 (gate is now asserted)
  ;; [a-> '()] from state [a = '()  b = '() g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2320 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2321 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2322 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state (redundnant)
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2323 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2324 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2325 failing\n"))
  ;; [a-> #t] from state [a = '()  b = '() g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; b should also be #t
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2326 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2327 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2328 failing\n"))
  (begin ((a 'set-signal!) '() 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2329 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2330 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2331 failing\n"))
  ;; [a-> #f] from state [a = '()  b = '() g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; b should also be #f
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2332 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2333 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2334 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2335 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2336 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2337 failing\n"))
  ;; state 20 state [a = #t  b = '() g = #f ] cannot be reached
  ;; state 21 state [a = #f  b = '() g = #f ] cannot be reached
  ;; state 22 state [a = '()  b = #t g = #f ] cannot be reached
  ;; state 23
  ;; [a-> '()] from state [a = #t  b = #t g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!)) ; b should also be '()
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2338 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2339 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2340 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2341 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2342 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2343 failing\n"))
  ;; [a-> #t] from state [a = #t  b = #t g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; b should also be #t
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2344 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2345 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2346 failing\n"))
  (begin ((a 'set-signal!) #t 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2347 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2348 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2349 failing\n"))
  ;; [a-> #f] from state [a = #t  b = #t g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; b should also be #f
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2350 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2351 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2352 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2353 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2354 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2355 failing\n"))
  ;; state 24 [a = #f  b = #t g = #f ] cannot be reached
  ;; state 25 [a = '() b = #f g = #f ] cannot be reached
  ;; state 26 [a = #t  b = #f g = #f ] cannot be reached
  ;; state 27
  ;; [a-> '()] from state [a = #f  b = #f g = #f ]
  (begin ((a 'set-signal!) '() 'x) (global 'propagate!)) ; b should also be '()
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2356 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2357 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2358 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2359 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2360 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2361 failing\n"))
  ;; [a-> #t] from state [a = #f  b = #f g = #f ]
  (begin ((a 'set-signal!) #t 'x) (global 'propagate!)) ; b should also be #t
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2362 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2363 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2364 failing\n"))
  (begin ((a 'set-signal!) #f 'x)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2365 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2366 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2367 failing\n"))
  ;; [a-> #f] from state [a = #f  b = #f g = #f ]
  (begin ((a 'set-signal!) #f 'x) (global 'propagate!)) ; b should also be #f
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2368 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2369 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2370 failing\n"))
  (begin ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) '() 'y)
         ((g 'set-signal!) '() 'z)
         (global 'propagate!)) ; setting next state
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2371 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2372 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2373 failing\n"))
  ;;
  ;; b transitions
  ;; state 1
  ;; [b-> '()] from state [b = '() a = '() g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2404 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2405 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2406 failing\n"))
  ;; [b-> #t] from state [b = '() a = '() g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2407 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2408 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2409 failing\n"))
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2410 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2411 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2412 failing\n"))
  ;; [b-> #f] from state [b = '() a = '() g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2413 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2414 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2415 failing\n"))
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2416 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2417 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2418 failing\n"))
  ;; state 2
  ;; [b-> '()] from state [b = #t a = '() g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2419 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2420 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2421 failing\n"))
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2422 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2423 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2424 failing\n"))
  ;; [b-> #t] from state [b = #t a = '() g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2425 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2426 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2427 failing\n"))
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2428 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2429 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2430 failing\n"))
  ;; [b-> #f] from state [b = #t a = '() g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2431 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2432 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2433 failing\n"))
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2434 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2435 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2436 failing\n"))
  ;; state 3
  ;; [b-> '()] from state [b = #f a = '() g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2437 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2438 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2439 failing\n"))
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2440 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2441 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2442 failing\n"))
  ;; [b-> #t] from state [b = #f a = '() g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2443 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2444 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2445 failing\n"))
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2446 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2447 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2448 failing\n"))
  ;; [b-> #f] from state [b = #f a = '() g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2449 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2450 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2451 failing\n"))
  (begin ((b 'set-signal!) '() 'y)((a 'set-signal!) #t 'x) (global 'propagate!)) ; next
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2452 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2453 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2454 failing\n"))
  ;; state 4
  ;; [b-> '()] from state [b = '() a = #t g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2455 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2456 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2457 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2459 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2460 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2461 failing\n"))
  ;; [b-> #t] from state [b = '() a = #t g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2462 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2463 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2464 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2465 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2466 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2467 failing\n"))
  ;; [b-> #f] from state [b = '() a = #t g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2469 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2470 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2471 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2472 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2473 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2474 failing\n"))
  ;; state 5
  ;; [b-> '()] from state [b = #t a = #t g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2475 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2476 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2477 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2478 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2479 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2480 failing\n"))
  ;; [b-> #t] from state [b = #t a = #t g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2481 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2482 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2483 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2484 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2485 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2486 failing\n"))
  ;; [b-> #f] from state [b = #t a = #t g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2487 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2488 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2489 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2490 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2491 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2492 failing\n"))
  ;; state 6
  ;; [b-> '()] from state [b = #f a = #t g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2493 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2494 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2495 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2496 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2497 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2498 failing\n"))
  ;; [b-> #t] from state [b = #f a = #t g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2499 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2500 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2501 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2502 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2503 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2504 failing\n"))
  ;; [b-> #f] from state [b = #f a = #t g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2505 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2506 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2507 failing\n"))
  (begin ((b 'set-signal!) '() 'y)((a 'set-signal!) #f 'x)(global 'propagate!)) ; next
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2508 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2509 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2510 failing\n"))
  ;; state 7
  ;; [b-> '()] from state [b = '() a = #f g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2511 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2512 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2513 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2514 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2515 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2516 failing\n"))
  ;; [b-> #t] from state [b = '() a = #f g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2517 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2518 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2519 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2520 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2521 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2522 failing\n"))
  ;; [b-> #f] from state [b = '() a = #f g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2523 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2524 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2525 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2526 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2527 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2528 failing\n"))
  ;; state 8
  ;; [b-> '()] from state [b = #t a = #f g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2529 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2530 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2531 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2532 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2533 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2534 failing\n"))
  ;; [b-> #t] from state [b = #t a = #f g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2535 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2536 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2537 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2538 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2539 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2540 failing\n"))
  ;; [b-> #f] from state [b = #t a = #f g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2541 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2542 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2543 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2544 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2545 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2546 failing\n"))
  ;; state 9
  ;; [b-> '()] from state [b = #f a = #f g = '()]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2541 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2542 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2543 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2544 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2545 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2546 failing\n"))
  ;; [b-> #t] from state [b = #f a = #f g = '()]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2547 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2548 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2549 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2550 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2551 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2552 failing\n"))
  ;; [b-> #f] from state [b = #f a = #f g = '()]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2553 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2554 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2555 failing\n"))
  (begin ((b 'set-signal!) '() 'y)
         ((a 'set-signal!) '() 'x)
         ((g 'set-signal!) #t  'z)
         (global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2555 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2556 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2557 failing\n"))
  ;; state 10
  ;; [b-> '()] from state [b = '() a = '() g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2558 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2559 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2560 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2561 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2562 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2563 failing\n"))
  ;; [b-> #t] from state [b = '() a = '() g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2564 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2565 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2566 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2567 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2568 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2569 failing\n"))
  ;; [b-> #f] from state [b = '() a = '() g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2570 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2571 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2572 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2573 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2574 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2575 failing\n"))
  ;; state 11
  ;; [b-> '()] from state [b = #t a = '() g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2576 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2577 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2578 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2579 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2580 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2581 failing\n"))
  ;; [b-> #t] from state [b = #t a = '() g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2582 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2583 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2584 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2585 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2586 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2587 failing\n"))
  ;; [b-> #f] from state [b = #t a = '() g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2588 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2589 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2590 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2591 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2592 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2593 failing\n"))
  ;; state 12
  ;; [b-> '()] from state [b = #f a = '() g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2594 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2595 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2596 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2597 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2598 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2599 failing\n"))
  ;; [b-> #t] from state [b = #f a = '() g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2600 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2601 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2602 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2603 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2604 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2605 failing\n"))
  ;; [b-> #f] from state [b = #f a = '() g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2606 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2607 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2608 failing\n"))
  (begin ((b 'set-signal!) '() 'y)((a 'set-signal!) #t 'x)(global 'propagate!)) ; next
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2609 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2610 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2611 failing\n"))
  ;; state 13
  ;; [b-> '()] from state [b = '() a = #t g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2612 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2613 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2614 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2615 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2616 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2617 failing\n"))
  ;; [b-> #t] from state [b = '() a = #t g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2618 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2619 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2620 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2621 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2622 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2623 failing\n"))
  ;; [b-> #f] from state [b = '() a = #t g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2624 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2625 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2626 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2627 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2628 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2629 failing\n"))
  ;; state 14
  ;; [b-> '()] from state [b = #t  a = #t g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2630 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2631 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2632 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2633 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2634 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2635 failing\n"))
  ;; [b-> #t] from state [b = #t  a = #t g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2636 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2637 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2638 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2639 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2640 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2641 failing\n"))
  ;; [b-> #f] from state [b = #t  a = #t g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2642 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2643 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2644 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2645 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2646 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2647 failing\n"))
  ;; state 15
  ;; [b-> '()] from state [b = #f  a = #t g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2648 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2649 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2650 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2651 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2652 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2653 failing\n"))
  ;; [b-> #t] from state [b = #f  a = #t g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2654 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2655 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2656 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2657 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2658 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2659 failing\n"))
  ;; [b-> #f] from state [b = #f  a = #t g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2660 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2661 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2662 failing\n"))
  (begin ((b 'set-signal!) '() 'y)((a 'set-signal!) #f 'x)(global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2663 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2664 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2665 failing\n"))
  ;; state 16
  ;; [b-> '()] from state [b = '()  a = #f g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2666 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2667 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2668 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2669 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2670 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2671 failing\n"))
  ;; [b-> #t] from state [b = '()  a = #f g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2672 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2673 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2674 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2675 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2676 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2677 failing\n"))
  ;; [b-> #f] from state [b = '()  a = #f g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2678 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2679 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2680 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2681 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2682 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2683 failing\n"))
  ;; state 17
  ;; [b-> '()] from state [b = #t  a = #f g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2684 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2685 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2686 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2687 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2688 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2689 failing\n"))
  ;; [b-> #t] from state [b = #t  a = #f g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2690 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2691 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2692 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2693 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2694 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2695 failing\n"))
  ;; [b-> #f] from state [b = #t  a = #f g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2696 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2697 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2698 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2699 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2700 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2701 failing\n"))
  ;; state 18
  ;; [b-> '()] from state [b = #f  a = #f g = #t ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2702 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2703 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2704 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2705 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2706 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2707 failing\n"))
  ;; [b-> #t] from state [b = #f  a = #f g = #t ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2708 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2709 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2710 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2711 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2712 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2713 failing\n"))
  ;; [b-> #f] from state [b = #f  a = #f g = #t ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2714 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2715 failing\n"))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2716 failing\n"))
  (begin ((b 'set-signal!) '() 'y)
         ((a 'set-signal!) '() 'x)
         ((g 'set-signal!) #f  'z)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2717 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2718 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2719 failing\n"))
  ;; state 19 (gate is now asserted)
  ;; [b-> '()] from state [b = '()  a = '() g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2720 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2721 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2722 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2723 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2724 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2725 failing\n"))
  ;; [b-> #t] from state [b = '()  a = '() g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; a should also be #t
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2726 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2727 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2728 failing\n"))
  (begin ((b 'set-signal!) '() 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2729 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2730 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2731 failing\n"))
  ;; [b-> #f] from state [b = '()  a = '() g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; a should also be #f
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2732 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2733 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2734 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2735 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2736 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2737 failing\n"))
  ;; state 20 state [b = #t  a = '() g = #f ] cannot be reached
  ;; state 21 state [b = #f  a = '() g = #f ] cannot be reached
  ;; state 22 state [b = '()  a = #t g = #f ] cannot be reached
  ;; state 23
  ;; [b-> '()] from state [b = #t  a = #t g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!)) ; a should also be '()
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2738 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2739 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2740 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2741 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2742 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2743 failing\n"))
  ;; [b-> #t] from state [b = #t  a = #t g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; a should also be #t
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2744 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2745 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2746 failing\n"))
  (begin ((b 'set-signal!) #t 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2747 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2748 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2749 failing\n"))
  ;; [b-> #f] from state [b = #t  a = #t g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; a should also be #f
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2750 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2751 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2752 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state (redundant)
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2753 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2754 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2755 failing\n"))
  ;; state 24 [b = #f  a = #t g = #f ] cannot be reached
  ;; state 25 [b = '() a = #f g = #f ] cannot be reached
  ;; state 26 [b = #t  a = #f g = #f ] cannot be reached
  ;; state 27
  ;; [b-> '()] from state [b = #f  a = #f g = #f ]
  (begin ((b 'set-signal!) '() 'y) (global 'propagate!)) ; a should also be '()
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2756 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2757 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2758 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2759 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2760 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2761 failing\n"))
  ;; [b-> #t] from state [b = #f  a = #f g = #f ]
  (begin ((b 'set-signal!) #t 'y) (global 'propagate!)) ; a should also be #t
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2762 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2763 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2764 failing\n"))
  (begin ((b 'set-signal!) #f 'y)(global 'propagate!)) ; setting next state
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2765 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2766 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2767 failing\n"))
  ;; [b-> #f] from state [b = #f  a = #f g = #f ]
  (begin ((b 'set-signal!) #f 'y) (global 'propagate!)) ; a should also be #f
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2768 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2769 failing\n"))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2770 failing\n"))
  (begin ((b 'set-signal!) '() 'y)
         ((a 'set-signal!) '() 'x)
         ((g 'set-signal!) '() 'z)
         (global 'propagate!)) ; setting next state
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2771 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2772 failing\n"))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2773 failing\n"))
  ;;
  ;; g transitions
  ;; state 1
  ;; [g-> '()] from state [g = '() a = '() b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2804 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2805 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2806 failing\n"))
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2807 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2808 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2809 failing\n"))
  ;; [g-> #t] from state [g = '() a = '() b = '()]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2810 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2811 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2812 failing\n"))
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2813 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2814 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2815 failing\n"))
  ;; [g-> #f] from state [g = '() a = '() b = '()]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2816 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2817 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2818 failing\n"))
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2819 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2820 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2821 failing\n"))
  ;; state 2
  ;; [g-> '()] from state [g = #t a = '() b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2822 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2823 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2824 failing\n"))
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2825 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2826 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2827 failing\n"))
  ;; [g-> #t] from state [g = #t a = '() b = '()]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2828 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2829 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2830 failing\n"))
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2831 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2832 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2833 failing\n"))
  ;; [g-> #f] from state [g = #t a = '() b = '()]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2834 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2835 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2836 failing\n"))
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2837 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2838 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2839 failing\n"))
  ;; state 3
  ;; [g-> '()] from state [g = #f a = '() b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2840 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2841 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2842 failing\n"))
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2843 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2844 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2845 failing\n"))
  ;; [g-> #t] from state [g = #f a = '() b = '()]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2846 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2847 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2848 failing\n"))
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!)) ; setting next state
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2849 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2850 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2851 failing\n"))
  ;; [g-> #f] from state [g = #f a = '() b = '()]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2852 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2853 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2854 failing\n"))
  (begin ((g 'set-signal!) '() 'z)((a 'set-signal!) #t 'x)(global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2855 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2856 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2857 failing\n"))
  ;; state 4
  ;; [g-> '()] from state [g = '() a = #t b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2858 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2859 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2860 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2861 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2862 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2863 failing\n"))
  ;; [g-> #t] from state [g = '() a = #t b = '()]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2864 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2865 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2866 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; setting next state
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2867 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2868 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2869 failing\n"))
  ;; [g-> #f] from state [g = '() a = #t b = '()] (b should be #t)
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2870 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2871 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2872 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2873 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2874 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2875 failing\n"))
  ;; state 5
  ;; [g-> '()] from state [g = #t a = #t b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2876 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2877 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2878 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2879 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2880 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2881 failing\n"))
  ;; [g-> #t] from state [g = #t a = #t b = '()]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2882 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2883 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2884 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; setting next state
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2885 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2886 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2887 failing\n"))
  ;; [g-> #f] from state [g = #t a = #t b = '()] (b should be #t)
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2888 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2889 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2890 failing\n"))
  (begin ((g 'set-signal!) '() 'z)((a 'set-signal!) #f 'x)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2891 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2892 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2893 failing\n"))
  ;; state 6 state [g = #f a = #t b = '()] cannot be reached
  ;; state 7
  ;; [g-> '()] from state [g = '() a = #f b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2894 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2895 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2896 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2897 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2898 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2899 failing\n"))
  ;; [g-> #t] from state [g = '() a = #f b = '()]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2900 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2901 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2902 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2903 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2904 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2905 failing\n"))
  ;; [g-> #f] from state [g = '() a = #f b = '()] (b should be #f)
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2906 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2907 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2908 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2909 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2910 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2911 failing\n"))
  ;; state 8
  ;; [g-> '()] from state [g = #t a = #f b = '()]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2912 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2913 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2914 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2915 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2916 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2917 failing\n"))
  ;; [g-> #t] from state [g = #t a = #f b = '()]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2918 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2919 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2920 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2921 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2922 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 2923 failing\n"))
  ;; [g-> #f] from state [g = #t a = #f b = '()] (b should be #f)
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2924 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 2925 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 2926 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!) ; one more propagate!
         ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) #t  'y)(global 'propagate!))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2927 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2928 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2929 failing\n"))
  ;; state 9 state [g = #f a = #f b = '()] cannot be reached
  ;; state 10
  ;; [g-> '()] from state [g = '() a = '() b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2930 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2931 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2932 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2933 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2934 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2935 failing\n"))
  ;; [g-> #t] from state [g = '() a = '() b = #t]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2936 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2937 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2938 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2939 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2940 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2941 failing\n"))
  ;; [g-> #f] from state [g = '() a = '() b = #t] (a should be #t)
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2942 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2943 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2944 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2945 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2946 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2947 failing\n"))
  ;; state 11
  ;; [g-> '()] from state [g = #t a = '() b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2948 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2949 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2950 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2951 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2952 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2953 failing\n"))
  ;; [g-> #t] from state [g = #t a = '() b = #t]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2954 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2955 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2956 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next (redundant)
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2957 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 2958 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2959 failing\n"))
  ;; [g-> #f] from state [g = #t a = '() b = #t] (a should be #t)
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2960 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2961 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2962 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!) ; one more propagate!
         ((a 'set-signal!) #t 'x)(global 'propagate!)) ; as otherwise this fails
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2963 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2964 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2965 failing\n"))
  ;; state 12 state [g = #f a = '() b = #t] cannot be reached
  ;; state 13
  ;; [g-> '()] from state [g = '() a = #t b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2966 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2967 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2968 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next (redundant)
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2969 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2970 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2971 failing\n"))
  ;; [g-> #t] from state [g = '() a = #t b = #t]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2972 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2973 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2974 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2975 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2976 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2977 failing\n"))
  ;; [g-> #f] from state [g = '() a = #t b = #t]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2978 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2979 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2980 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2981 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2982 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2983 failing\n"))
  ;; state 14
  ;; [g-> '()] from state [g = #t a = #t b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 2984 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2985 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2986 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2987 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2988 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2989 failing\n"))
  ;; [g-> #t] from state [g = #t a = #t b = #t]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2990 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2991 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2992 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next (redundant)
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 2993 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2994 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2995 failing\n"))
  ;; [g-> #f] from state [g = #t a = #t b = #t]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2996 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 2997 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 2998 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 2999 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3000 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3001 failing\n"))
  ;; state 15
  ;; [g-> '()] from state [g = #f a = #t b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3002 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3003 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3004 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3005 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3006 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3007 failing\n"))
  ;; [g-> #t] from state [g = #f a = #t b = #t]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3009 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3010 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3011 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3012 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3013 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3014 failing\n"))
  ;; [g-> #f] from state [g = #f a = #t b = #t]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3015 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3016 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3017 failing\n"))
  (begin ((g 'set-signal!) '() 'z)((a 'set-signal!) #f 'x)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3018 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3019 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3020 failing\n"))
  ;; state 16
  ;; [g-> '()] from state [g = '() a = #f b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3021 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3022 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3023 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3024 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3025 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3026 failing\n"))
  ;; [g-> #t] from state [g = '() a = #f b = #t]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3027 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3028 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3029 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3030 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3031 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3032 failing\n"))
  ;; [g-> #f] from state [g = '() a = #f b = #t] (short circuit)
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(= 0(global 'error-count)))(display"transistor:unit-test 3033 failing\n"))
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(= 2(global 'error-count)))(display"transistor:unit-test 3034 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3035 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3036 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3037 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3038 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3039 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3040 failing\n"))
  ;; state 17
  ;; [g-> '()] from state [g = #t a = #f b = #t]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3041 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3042 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3043 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3044 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3045 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3046 failing\n"))
  ;; [g-> #t] from state [g = #t a = #f b = #t]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3047 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3048 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3049 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3050 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3051 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3052 failing\n"))
  ;; [g-> #f] from state [g = #t a = #f b = #t]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(= 2(global 'error-count)))(display"transistor:unit-test 3053 failing\n"))
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(= 4(global 'error-count)))(display"transistor:unit-test 3054 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3055 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3056 failing\n"))
  (if(not(eq? #t (b 'get-signal)))(display"transistor: unit-test 3057 failing\n"))
  (begin ((g 'set-signal!) '() 'z)
         ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) #f  'y)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3058 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3059 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3060 failing\n"))
  ;; state 18 state [g = #f a = #f b = #t] cannot be reached
  ;; well in fact this state can be reached which is a flaw
  ;; propagate! will generate 2 error messages. However subsequent propagate!
  ;; will provide no further warning and state [g = #f a = #f b = #t]
  ;; will be maintained despite being inconsistent.
  ;; state 19
  ;; [g-> '()] from state [g = '() a = '() b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3061 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3062 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3063 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3064 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3065 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3066 failing\n"))
  ;; [g-> #t] from state [g = '() a = '() b = #f]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3067 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3068 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3069 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3070 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3071 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3072 failing\n"))
  ;; [g-> #f] from state [g = '() a = '() b = #f] (a should be #f)
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3073 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3074 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3075 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3076 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3077 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3078 failing\n"))
  ;; state 20
  ;; [g-> '()] from state [g = #t a = '() b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3079 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3080 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3081 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3082 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3083 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3084 failing\n"))
  ;; [g-> #t] from state [g = #t a = '() b = #f]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3085 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3086 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3087 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3088 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3089 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3090 failing\n"))
  ;; [g-> #f] from state [g = #t a = '() b = #f] (a should be #f)
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3091 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3092 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3093 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)  ; one more propagate!
         ((a 'set-signal!) #t 'x) (global 'propagate!))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3094 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3095 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3096 failing\n"))
  ;; state 21 state [g = #f a = '() b = #f] cannot be reached
  ;; state 22
  ;; [g-> '()] from state [g = '() a = #t b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3097 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3098 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3099 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3100 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3101 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3102 failing\n"))
  ;; [g-> #t] from state [g = '() a = #t b = #f]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3103 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3104 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3105 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3106 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3107 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3108 failing\n"))
  ;; [g-> #f] from state [g = '() a = #t b = #f]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(= 4(global 'error-count)))(display"transistor:unit-test 3109 failing\n"))
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(= 6(global 'error-count)))(display"transistor:unit-test 3111 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3112 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3113 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3114 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3115 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3116 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3117 failing\n"))
  ;; state 23
  ;; [g-> '()] from state [g = #t a = #t b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3118 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3119 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3120 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3121 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3122 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3123 failing\n"))
  ;; [g-> #t] from state [g = #t a = #t b = #f]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3124 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3125 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3126 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3127 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3128 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3129 failing\n"))
  ;; [g-> #f] from state [g = #t a = #t b = #f]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(= 6(global 'error-count)))(display"transistor:unit-test 3130 failing\n"))
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(= 8(global 'error-count)))(display"transistor:unit-test 3131 failing\n"))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3132 failing\n"))
  (if(not(eq? #t (a 'get-signal)))(display"transistor: unit-test 3133 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3134 failing\n"))
  (begin ((g 'set-signal!)'() 'z)((a 'set-signal!) #f 'x) (global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3135 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3136 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3137 failing\n"))
  ;; state 24 state [g = #f a = #t b = #f] cannot be reached
  ;; well in fact this state can be reached which is a flaw
  ;; propagate! will generate 2 error messages. However subsequent propagate!
  ;; will provide no further warning and state [g = #f a = #f b = #t]
  ;; will be maintained despite being inconsistent.
  ;; state 25
  ;; [g-> '()] from state [g = '() a = #f b = #f]
  (begin ((g 'set-signal!) '()'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3138 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3139 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3140 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3141 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3142 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3143 failing\n"))
  ;; [g-> #t] from state [g = '() a = #f b = #f]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3144 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3145 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3146 failing\n"))
  (begin ((g 'set-signal!) '() 'z)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3147 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3148 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3149 failing\n"))
  ;; [g-> #f] from state [g = '() a = #f b = #f]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3150 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3151 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3152 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3153 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3154 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3155 failing\n"))
  ;; state 26
  ;; [g-> '()] from state [g = #t a = #f b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3156 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3157 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3158 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3159 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3160 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3161 failing\n"))
  ;; [g-> #t] from state [g = #t a = #f b = #f]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3162 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3163 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3164 failing\n"))
  (begin ((g 'set-signal!) #t 'z)(global 'propagate!)) ; next
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3165 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3166 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3167 failing\n"))
  ;; [g-> #f] from state [g = #t a = #f b = #f]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3169 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3170 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3171 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3172 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3173 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3174 failing\n"))
  ;; state 27
  ;; [g-> '()] from state [g = #f a = #f b = #f]
  (begin ((g 'set-signal!) '() 'z) (global 'propagate!))
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3175 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3176 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3177 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3178 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3179 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3180 failing\n"))
  ;; [g-> #t] from state [g = #f a = #f b = #f]
  (begin ((g 'set-signal!) #t 'z) (global 'propagate!))
  (if(not(eq? #t (g 'get-signal)))(display"transistor: unit-test 3181 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3182 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3183 failing\n"))
  (begin ((g 'set-signal!) #f 'z)(global 'propagate!)) ; next
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3184 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3185 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3186 failing\n"))
  ;; [g-> #f] from state [g = #f a = #f b = #f]
  (begin ((g 'set-signal!) #f 'z) (global 'propagate!))
  (if(not(eq? #f (g 'get-signal)))(display"transistor: unit-test 3187 failing\n"))
  (if(not(eq? #f (a 'get-signal)))(display"transistor: unit-test 3188 failing\n"))
  (if(not(eq? #f (b 'get-signal)))(display"transistor: unit-test 3189 failing\n"))
  (begin ((g 'set-signal!) '() 'z)
         ((a 'set-signal!) '() 'x)
         ((b 'set-signal!) '() 'y)(global 'propagate!)) ; next
  (if(not(eq? '()(g 'get-signal)))(display"transistor: unit-test 3190 failing\n"))
  (if(not(eq? '()(a 'get-signal)))(display"transistor: unit-test 3191 failing\n"))
  (if(not(eq? '()(b 'get-signal)))(display"transistor: unit-test 3192 failing\n"))
  )

(transistor-test)
(exit 0)
