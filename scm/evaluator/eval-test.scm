(load "eval.scm")
(load "environment-test.scm")
(load "primitive-test.scm")
(load "global-env-test.scm")

(define (eval-test)
  ;
  (display "eval: starting unit test\n")
  ;
  ; self-evaluating
  ;
  (let ((x (eval 3 global-env)))
    (if (not (equal? x 3)) (display "eval: unit test 1.0 failing\n")))
  (let ((x (eval 3.5 global-env)))
    (if (not (equal? x 3.5)) (display "eval: unit test 1.1 failing\n")))
  (let ((x (eval "hello" global-env)))
    (if (not (equal? x "hello")) (display "eval: unit test 1.2 failing\n")))
  (let ((x (eval "hello\n" global-env)))
    (if (not (equal? x "hello\n")) (display "eval: unit test 1.3 failing\n")))
  (let ((x (eval #\a global-env)))
    (if (not (equal? x #\a)) (display "eval: unit test 1.4 failing\n")))
  (let ((x (eval #t global-env)))
    (if (not (equal? x #t)) (display "eval: unit test 1.5 failing\n")))
  (let ((x (eval #f global-env)))
    (if (not (equal? x #f)) (display "eval: unit test 1.6 failing\n")))
  ;
  ; variable
  ;
  (let ((x (eval 'car global-env)))
    (if (not (equal? (primitive-implementation x) car)) 
        (display "eval: unit test 2.0 failing\n")))
  (let ((x (eval 'cdr global-env)))
    (if (not (equal? (primitive-implementation x) cdr)) 
        (display "eval: unit test 2.1 failing\n")))
  (let ((x (eval 'cons global-env)))
    (if (not (equal? (primitive-implementation x) cons)) 
        (display "eval: unit test 2.2 failing\n")))
  (let ((x (eval 'null? global-env)))
    (if (not (equal? (primitive-implementation x) null?)) 
        (display "eval: unit test 2.3 failing\n")))
  (let ((x (eval '+ global-env)))
    (if (not (equal? (primitive-implementation x) +)) 
        (display "eval: unit test 2.4 failing\n")))
  (let ((x (eval '* global-env)))
    (if (not (equal? (primitive-implementation x) *)) 
        (display "eval: unit test 2.5 failing\n")))
  (let ((x (eval '- global-env)))
    (if (not (equal? (primitive-implementation x) -)) 
        (display "eval: unit test 2.6 failing\n")))
  (let ((x (eval '/ global-env)))
    (if (not (equal? (primitive-implementation x) /)) 
        (display "eval: unit test 2.7 failing\n")))
  (let ((x (eval 'modulo global-env)))
    (if (not (equal? (primitive-implementation x) modulo)) 
        (display "eval: unit test 2.8 failing\n")))
  ;
  ; quoted
  ;
  (let ((x (eval (quote 'hello) global-env)))
    (if (not (equal? x 'hello)) (display "eval: unit test 3.0 failing\n")))
  (let ((x (eval ''hello global-env)))
    (if (not (equal? x 'hello)) (display "eval: unit test 3.1 failing\n")))
  (let ((x (eval ''(list cons 3 "abc" #\a #t) global-env)))
    (if (not (equal? x '(list cons 3 "abc" #\a #t)))
      (display "eval: unit test 3.2 failing\n")))
  ;
  ; assigment
  ;
  (let ((saved-value (eval 'modulo global-env)))
    ; redefining primitive in global-env
    (let ((x (eval '(set! modulo 'any-value) global-env)))
      (if (not (equal? (eval 'modulo global-env) 'any-value))
        (display "eval: unit test 4.0 failing\n"))
    ; restoring primitive
      ((global-env 'set!) 'modulo saved-value)
      (let ((x (eval 'modulo global-env)))
        (if (not (equal? (primitive-implementation x) modulo)) 
          (display "eval: unit test 4.1 failing\n")))))
  ;
  ; definition
  ;
  (let ((x (eval '(define var1 12) global-env)))
    (if (not (equal? (eval 'var1 global-env) 12))
      (display "eval: unit test 5.0 failing\n")))
  (let ((x (eval '(define var2 0.3) global-env)))
    (if (not (equal? (eval 'var2 global-env) 0.3))
      (display "eval: unit test 5.1 failing\n")))
  (let ((x (eval '(define var3 "hello") global-env)))
    (if (not (equal? (eval 'var3 global-env) "hello"))
      (display "eval: unit test 5.2 failing\n")))
  (let ((x (eval '(define var4 #\a) global-env)))
    (if (not (equal? (eval 'var4 global-env) #\a))
      (display "eval: unit test 5.3 failing\n")))
  (let ((x (eval '(define var5 #t) global-env)))
    (if (not (equal? (eval 'var5 global-env) #t))
      (display "eval: unit test 5.4 failing\n")))
  (let ((x (eval '(define var6 #f) global-env)))
    (if (not (equal? (eval 'var6 global-env) #f))
      (display "eval: unit test 5.5 failing\n")))
  ((global-env 'delete!) 'var1)
  ((global-env 'delete!) 'var2)
  ((global-env 'delete!) 'var3)
  ((global-env 'delete!) 'var4)
  ((global-env 'delete!) 'var5)
  ((global-env 'delete!) 'var6)
 

  (display "eval: unit test complete\n"))

;(environment-test)
;(primitive-test)
;(global-env-test)
(eval-test)
(exit 0)
