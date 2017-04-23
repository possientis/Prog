(require 'object->string)

(load "main.scm")

(define (assert-equals left right message)
  (if (not (equal? left right)) 
    (error "unit-test failure: "
           (string-append message 
                          ": value = " (object->string left)
                          ": expected = " (object->string right)))))
(define (unit-test)
  ;
  (newline)
  (display "unit-test: starting test\n")
  ; true
  (assert-equals (evaluate #t) #t "true.0")
  ; false
  (assert-equals (evaluate #f) #f "false.0")
  ; if
  (assert-equals (evaluate '(if #t #f #t)) #f "if.0")
  (assert-equals (evaluate '(if #t #t #f)) #t "if.1")
  (assert-equals (evaluate '(if #f #t #f)) #f "if.2")
  (assert-equals (evaluate '(if #f #f #t)) #t "if.3")
  ; 0
  (assert-equals (evaluate 0) 0 "zero.0")
  ; succ
  (assert-equals (evaluate '(succ 0)) 1 "succ.0")
  ; pred
  (assert-equals (evaluate '(pred (succ (succ 0)))) 1 "pred.0")
  ; zero?
  (assert-equals (evaluate '(zero? 0)) #t "zero?.0")
  (assert-equals (evaluate '(zero? (succ 0))) #f "zero?.1")
  
  
  (display "unit-test: test complete\n"))

(unit-test)

(exit 0)
