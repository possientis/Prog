(load "main.scm")

(define (assert-equal left right message)
  (if (not (equal? left right)) 
    (error "unit-test failure: "
           (string-append message 
                          ": value = " (object->string left)
                          ": expected = " (object->string right)))))

(define (test-expression exp value message)
  (let ((print (lambda (msg) (string-append message msg)))
        (mode (get-eval-mode))) ; save eval mode to be restored
    (assert-equal (strict-eval exp) value (print ": strict-eval")) 
    (assert-equal (force-thunk (lazy-eval exp)) value (print ": lazy-eval")) 
    (assert-equal ((analyze exp) global-env) value (print ": analyze"))
    (set-eval-mode 'strict)
    (assert-equal (new-eval exp) value (print ": new-eval (strict)"))
    (set-eval-mode 'lazy)
    (assert-equal (force-thunk (new-eval exp)) value (print ": new-eval (lazy)"))
    (set-eval-mode 'analyze)
    (assert-equal (new-eval exp) value (print ": new-eval (analyze)"))
    (set-eval-mode mode)))  ; restoring eval mode

(define (unit-test)
  ;
  (newline)
  (display "unit-test: starting test\n")
  ;
  ; self-evaluating
  (display "testing self-evaluating expressions...\n")
  (test-expression '3 3 "self-evaluating")
  (test-expression '3.5 3.5 "self-evaluating")
  (test-expression '"hello" "hello" "self-evaluating")
  (test-expression '"hello\n" "hello\n" "self-evaluating")
  (test-expression '#\a #\a "self-evaluating")
  (test-expression '#t #t "self-evaluating")
  (test-expression '#f #f "self-evaluating")
  (let ((car-primitive (make-primitive-procedure car)))
    (test-expression car-primitive car-primitive  "self-evaluating"))
  (let ((eval-square (make-eval-procedure '(x) '(* x x) global-env)))
    (test-expression eval-square eval-square "self-evaluating"))
  (let ((analyze-square (make-analyze-procedure '(x) '(* x x) global-env)))
    (test-expression analyze-square analyze-square "self-evaluating"))
  ;
  ; variable
  (display "testing variable expressions...\n")
  (test-expression '+ (make-primitive-procedure +) "variable")
  (test-expression '* (make-primitive-procedure *) "variable")
  (test-expression '- (make-primitive-procedure -) "variable")
  (test-expression '/ (make-primitive-procedure /) "variable")
  (test-expression '= (make-primitive-procedure =) "variable")
  (test-expression '< (make-primitive-procedure <) "variable")
  (test-expression '> (make-primitive-procedure >) "variable")
  (test-expression '<= (make-primitive-procedure <=) "variable")
  (test-expression '>= (make-primitive-procedure >=) "variable")
  (test-expression 'append (make-primitive-procedure append) "variable")
  (test-expression 'apply (make-primitive-procedure new-apply) "variable")
  (test-expression 'boolean? (make-primitive-procedure boolean?) "variable")
  (test-expression 'caadr (make-primitive-procedure caadr) "variable")
  (test-expression 'caar (make-primitive-procedure caar) "variable")
  (test-expression 'cadddr (make-primitive-procedure cadddr) "variable")
  (test-expression 'caddr (make-primitive-procedure caddr) "variable")
  (test-expression 'cadr (make-primitive-procedure cadr) "variable")
  (test-expression 'car (make-primitive-procedure car) "variable")
  (test-expression 'cdadr (make-primitive-procedure cdadr) "variable")
  (test-expression 'cdar (make-primitive-procedure cdar) "variable")
  (test-expression 'cdr (make-primitive-procedure cdr) "variable")
  (test-expression 'cdddr (make-primitive-procedure cdddr) "variable")
  (test-expression 'cddr (make-primitive-procedure cddr) "variable")
  (test-expression 'char? (make-primitive-procedure char?) "variable")
  (test-expression 'close-port (make-primitive-procedure close-port) "variable")
  (test-expression 'cons (make-primitive-procedure cons) "variable")
  (test-expression 'display (make-primitive-procedure new-display) "variable")
  (test-expression 'eof-object? (make-primitive-procedure eof-object?) "variable")
  (test-expression 'eq? (make-primitive-procedure eq?) "variable")
  (test-expression 'equal? (make-primitive-procedure equal?) "variable")
  (test-expression 'error (make-primitive-procedure error) "variable")
  (test-expression 'eval (make-primitive-procedure new-eval) "variable")
  (test-expression 'exit (make-primitive-procedure exit) "variable")
  (test-expression 'hash (make-primitive-procedure hash) "variable")
  (test-expression 
    'inexact->exact (make-primitive-procedure inexact->exact) "variable")
  (test-expression 'length (make-primitive-procedure length) "variable")
  (test-expression 'list (make-primitive-procedure list) "variable")
  (test-expression 'load (make-primitive-procedure new-load) "variable")
  (test-expression 'make-vector (make-primitive-procedure make-vector) "variable")
  (test-expression 'map (make-primitive-procedure new-map) "variable")
  (test-expression 'modulo (make-primitive-procedure modulo) "variable")
  (test-expression 'newline (make-primitive-procedure newline) "variable")
  (test-expression 'null? (make-primitive-procedure null?) "variable")
  (test-expression 'number? (make-primitive-procedure number?) "variable")
  (test-expression 
    'number->string (make-primitive-procedure number->string) "variable")
  (test-expression 
    'object->string (make-primitive-procedure new-object->string) "variable")
  (test-expression 'open-file (make-primitive-procedure open-file) "variable")
  (test-expression 'pair? (make-primitive-procedure pair?) "variable")
  (test-expression 'read (make-primitive-procedure read) "variable")
  (test-expression 'require (make-primitive-procedure new-require) "variable")
  (test-expression 'reverse (make-primitive-procedure reverse) "variable")
  (test-expression 'set-car! (make-primitive-procedure set-car!) "variable")
  (test-expression 'set-cdr! (make-primitive-procedure set-cdr!) "variable")
  (test-expression 'string? (make-primitive-procedure string?) "variable")
  (test-expression 
    'string-append (make-primitive-procedure string-append) "variable")
  (test-expression 'symbol? (make-primitive-procedure symbol?) "variable")
  (test-expression 
    'vector-fill! (make-primitive-procedure vector-fill!) "variable")
  (test-expression 
    'vector-length (make-primitive-procedure vector-length) "variable")
  (test-expression 'vector-ref (make-primitive-procedure vector-ref) "variable")
  (test-expression 'vector-set! (make-primitive-procedure vector-set!) "variable")
  ;
  ; quoted
  (display "testing quoted expressions...\n") 
  ; the value of expression (quote hello) is (the symbol) hello
  (test-expression '(quote hello) 'hello "quoted")
  (test-expression (quote (quote hello))  (quote hello) "quoted")
  (test-expression (quote (quote hello)) 'hello "quoted")
  (test-expression (quote 'hello) 'hello "quoted")
  (test-expression ''hello 'hello "quoted")
  ; the value of expression (quote 3) is the integer 3
  (test-expression '(quote 3) 3 "quoted")
  (test-expression ''3 3 "quoted")
  ; the value of expression (quote 3.5) is the floating number 3.5
  (test-expression '(quote 3.5) 3.5 "quoted")
  (test-expression ''3.5 3.5 "quoted")
  ; the value of expression (quote #\a) is the character #\a
  (test-expression '(quote #\a) #\a "quoted")
  (test-expression ''#\a #\a "quoted")
  ; the value of expression (quote "hello") is the string "hello"
  (test-expression '(quote "hello") "hello" "quoted")
  (test-expression ''"hello" "hello" "quoted")
  ; the value of expression (quote #t) is the boolean value #t
  (test-expression '(quote #t) #t "quoted")
  (test-expression ''#t #t "quoted")
  ; the value of expression (quote #f) is the boolean value #f
  (test-expression '(quote #f) #f "quoted")
  (test-expression ''#f #f "quoted")
  ; the value of expression (quote (list 3)) is the expression (list 3)
  (test-expression '(quote (list 3)) '(list 3) "quoted")
  (test-expression ''(list 3) '(list 3) "quoted")
  (test-expression ''(list 3) (list 'list 3) "quoted")
  ; while the value of expression (list 3) is the value (list 3)
  (test-expression '(list 3) (list 3) "quoted")
  (test-expression '(list 3) '(3) "quoted")
  ; the value of expression (quote (list cons "abc" #\a)) is the expression
  ; (list cons "abc" #\a) which is not the same as the value (list cons "abc" #\a)
  (test-expression '(quote (list cons "abc" #\a)) '(list cons "abc" #\a) "quoted")
  (test-expression ''(list cons "abc" #\a) '(list cons "abc" #\a) "quoted")
  (test-expression ''(list cons "abc" #\a) (list 'list 'cons "abc" #\a) "quoted")
  ; the value (list cons "abc" #a) is the value of expression (list cons "abc" #\a)
  ; which is a list of three elements, where the first element is a value (an 
  ; object) representing the primitive operator 'cons'
  (test-expression '(list cons "abc" #\a) 
                   (list (make-primitive-procedure cons) "abc" #\a) "quoted")
  ; the value of the expression (quote (length (2 3))) is the expression 
  ; (length (2 3)). However, the expression (length (2 3)) cannot be evaluated
  ; as the expression (2 3) cannot be evaluated since 2 is not a valid operator
  (test-expression '(quote (length (2 3))) '(length (2 3)) "quoted")
  (test-expression '(quote (length (2 3))) (list 'length (list 2 3)) "quoted")
  ; the value of expression (quote (2 3)) is expression (2 3)
  (test-expression '(quote (2 3)) '(2 3) "quoted")
  (test-expression '(quote (2 3)) (list 2 3) "quoted")
  ; so the value of expression '(2 3) is the expression (2 3) 
  (test-expression ''(2 3) '(2 3) "quoted")
  (test-expression ''(2 3) (list 2 3) "quoted")
  ; the value of expression '(quote (length '(2 3))) is expression (length '(2 3))
  (test-expression '(quote (length '(2 3))) '(length '(2 3)) "quoted")
  (test-expression ''(length '(2 3)) '(length '(2 3)) "quoted")
  (test-expression ''(length (quote (2 3))) '(length '(2 3)) "quoted")
  (test-expression ''(length '(2 3)) '(length (quote (2 3))) "quoted")
  (test-expression 
    ''(length '(2 3)) (list 'length (list 'quote (list 2 3))) "quoted")
  ;
  ; assigment
  (display "testing assignment expressions...\n")
  ;
  ; eval
  (let ((saved-value (new-eval 'modulo)))
    ; redefining primitive in global-env
    (let ((x (new-eval '(set! modulo 'any-value))))
      (if (not (equal? (new-eval 'modulo) 'any-value))
        (display "unit-test: test 4.0 failing\n"))
    ; restoring primitive
      ((global-env 'set!) 'modulo saved-value)
      (let ((x (new-eval 'modulo global-env)))
        (if (not (equal? (primitive-procedure-object x) modulo)) 
          (display "unit-test: test 4.1 failing\n")))))

  ; analyze
  (let ((saved-value (new-eval 'modulo global-env)))
    ; redefining primitive in global-env
    (let ((x ((analyze '(set! modulo 'any-value)) global-env)))
      (if (not (equal? ((analyze 'modulo) global-env) 'any-value))
        (display "unit-test: test 4.2 failing\n"))
    ; restoring primitive
      ((global-env 'set!) 'modulo saved-value)
      (let ((x ((analyze 'modulo) global-env)))
        (if (not (equal? (primitive-procedure-object x) modulo)) 
          (display "unit-test: test 4.3 failing\n")))))
  ;
  ; definition
  (display "testing definition exprressions...\n")
  ;
  ; eval
  ; simple variable binding
  (let ((x (new-eval '(define var1 12))))
    (if (not (equal? (new-eval 'var1) 12))
      (display "unit-test: test 5.0 failing\n")))
  (let ((x (new-eval '(define var2 0.3))))
    (if (not (equal? (new-eval 'var2) 0.3))
      (display "unit-test: test 5.1 failing\n")))
  (let ((x (new-eval '(define var3 "hello"))))
    (if (not (equal? (new-eval 'var3) "hello"))
      (display "unit-test: test 5.2 failing\n")))
  (let ((x (new-eval '(define var4 #\a))))
    (if (not (equal? (new-eval 'var4) #\a))
      (display "unit-test: test 5.3 failing\n")))
  (let ((x (new-eval '(define var5 #t))))
    (if (not (equal? (new-eval 'var5) #t))
      (display "unit-test: test 5.4 failing\n")))
  (let ((x (new-eval '(define var6 #f))))
    (if (not (equal? (new-eval 'var6) #f))
      (display "unit-test: test 5.5 failing\n")))
  ((global-env 'delete!) 'var1)
  ((global-env 'delete!) 'var2)
  ((global-env 'delete!) 'var3)
  ((global-env 'delete!) 'var4)
  ((global-env 'delete!) 'var5)
  ((global-env 'delete!) 'var6)
  ; syntactic sugar for named functions
  (let ((x (new-eval '(define (f) 12))))
    (if (not (equal? (new-eval '(f)) 12))
      (display "unit-test: test 5.6 failing\n"))
    ((global-env 'delete!) 'f))
  (let ((x (new-eval '(define (f x) (* x x)))))
    (if (not (equal? (new-eval '(f 5)) 25))
      (display "unit-test: test 5.7 failing\n"))
    ((global-env 'delete!) 'f))
  (let ((x (new-eval '(define (f x y) (+ x y)))))
    (if (not (equal? (new-eval '(f 3 4)) 7))
      (display "unit-test: test 5.8 failing\n"))
    ((global-env 'delete!) 'f))
 
  ; analyze
  ; simple variable binding
  (let ((x ((analyze '(define var1 12)) global-env)))
    (if (not (equal? ((analyze 'var1) global-env) 12))
      (display "unit-test: test 5.9 failing\n")))
  (let ((x ((analyze '(define var2 0.3)) global-env)))
    (if (not (equal? ((analyze 'var2) global-env) 0.3))
      (display "unit-test: test 5.10 failing\n")))
  (let ((x ((analyze '(define var3 "hello")) global-env)))
    (if (not (equal? ((analyze 'var3) global-env) "hello"))
      (display "unit-test: test 5.11 failing\n")))
  (let ((x ((analyze '(define var4 #\a)) global-env)))
    (if (not (equal? ((analyze 'var4) global-env) #\a))
      (display "unit-test: test 5.12 failing\n")))
  (let ((x ((analyze '(define var5 #t)) global-env)))
    (if (not (equal? ((analyze 'var5) global-env) #t))
      (display "unit-test: test 5.13 failing\n")))
  (let ((x ((analyze '(define var6 #f)) global-env)))
    (if (not (equal? ((analyze 'var6) global-env) #f))
      (display "unit-test: test 5.14 failing\n")))
  ((global-env 'delete!) 'var1)
  ((global-env 'delete!) 'var2)
  ((global-env 'delete!) 'var3)
  ((global-env 'delete!) 'var4)
  ((global-env 'delete!) 'var5)
  ((global-env 'delete!) 'var6)
  ; syntactic sugar for named functions
 ;
  (let ((x ((analyze '(define (f) 12)) global-env)))   
    (if (not (equal? ((analyze '(f)) global-env) 12))
      (display "unit-test: test 5.18 failing\n"))
    ((global-env 'delete!) 'f))
  ;
  (let ((x ((analyze '(define (f x) (* x x))) global-env)))  
    (if (not (equal? ((analyze '(f 5)) global-env) 25))
      (display "unit-test: test 5.19 failing\n"))
    ((global-env 'delete!) 'f))
  ;
  (let ((x ((analyze '(define (f x y) (+ x y))) global-env)))
    (if (not (equal? ((analyze '(f 3 4)) global-env) 7))
      (display "unit-test: test 5.20 failing\n"))
    ((global-env 'delete!) 'f))
  ;
  ; if
  (display "testing if expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(if #t "yes" "no"))))
    (if (not (equal? x "yes")) (display "unit-test: test 6.0 failing\n")))
  (let ((x (new-eval '(if #f "yes" "no"))))
    (if (not (equal? x "no")) (display "unit-test: test 6.1 failing\n")))
  (let ((x (new-eval '(if #t "yes"))))
    (if (not (equal? x "yes")) (display "unit-test: test 6.2 failing\n")))
  (let ((x (new-eval '(if (equal? 3 3) (+ 2 3) (* 4 5)))))
    (if (not (equal? x 5)) (display "unit-test: test 6.3 failing\n")))
  (let ((x (new-eval '(if (equal? 3 4) (+ 2 3) (* 4 5)))))
    (if (not (equal? x 20)) (display "unit-test: test 6.4 failing\n")))
  
  ; analyze
  (let ((x ((analyze '(if #t "yes" "no")) global-env)))
    (if (not (equal? x "yes")) (display "unit-test: test 6.5 failing\n")))
  (let ((x ((analyze '(if #f "yes" "no")) global-env)))
    (if (not (equal? x "no")) (display "unit-test: test 6.6 failing\n")))
  (let ((x ((analyze '(if #t "yes")) global-env)))
    (if (not (equal? x "yes")) (display "unit-test: test 6.7 failing\n")))
  ((analyze '(if #f "yes")) global-env)
  (let ((x ((analyze '(if (equal? 3 3) (+ 2 3) (* 4 5))) global-env)))
    (if (not (equal? x 5)) (display "unit-test: test 6.8 failing\n")))
  (let ((x ((analyze '(if (equal? 3 4) (+ 2 3) (* 4 5))) global-env)))
    (if (not (equal? x 20)) (display "unit-test: test 6.9 failing\n")))
  ;
  ; not
  (display "testing not expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(not #t))))
    (if (not (equal? x #f)) (display "unit-test: test 7.0 failing\n")))
  (let ((x (new-eval '(not #f))))
    (if (not (equal? x #t)) (display "unit-test: test 7.1 failing\n")))

  ; analyze
  (let ((x ((analyze '(not #t)) global-env)))
    (if (not (equal? x #f)) (display "unit-test: test 7.2 failing\n")))
  (let ((x ((analyze '(not #f)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 7.3 failing\n")))
  ;
  ; lambda 
  (display "testing lambda expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(lambda () (+ 3 5)))))
    ((global-env 'define!) 'f x)
    (let ((y (new-eval '(f))))
      (if (not (equal? y 8)) (display "unit-test: test 8.0 failing\n")))
    ((global-env 'delete!) 'f))
  (let ((x (new-eval '(lambda (x) (* 3 x)))))
    ((global-env 'define!) 'f x)
    (let ((y (new-eval '(f 5))))
      (if (not (equal? y 15)) (display "unit-test: test 8.1 failing\n")))
    ((global-env 'delete!) 'f))
  (let ((x (new-eval '(lambda (x y) (+ x y)))))
    ((global-env 'define!) 'f x)
    (let ((y (new-eval '(f 3 4))))
      (if (not (equal? y 7)) (display "unit-test: test 8.2 failing\n")))
    ((global-env 'delete!) 'f))
  (let ((plus5 (new-eval '(lambda (x) (+ x y)) ((global-env 'extended)'(y)'(5)))))
    ((global-env 'define!) 'f plus5)
    (let ((y (new-eval '(f 6))))
      (if (not (equal? y 11)) (display "unit-test: test 8.3 failing\n")))
    ((global-env 'delete!) 'f))
  (let ((x (new-eval '((lambda () 45)))))
    (if (not (equal? x 45)) (display "unit-test: test 8.4 failing\n")))
  (let ((x (new-eval '((lambda (x) (+ x 7)) 5))))
    (if (not (equal? x 12)) (display "unit-test: test 8.5 failing\n")))
  (let ((x (new-eval '(let ((x 5)) ((lambda (u v) (+ u v)) x 6)))))
    (if (not (equal? x 11)) (display "unit-test: test 8.6 failing\n")))
  (let ((x (new-eval '(lambda arg (apply + arg)))))
    ((global-env 'define!) 'f x)
    (let ((y (new-eval '(f 1 2 3 4 5))))
      (if (not (equal? y 15)) (display "unit-test: test 8.6.1 failing\n")))
    ((global-env 'delete!) 'f))
  (let ((x (new-eval '(lambda (x y z . t) (+ x y z (apply + t))))))
    ((global-env 'define!) 'f x)
    (let ((y (new-eval '(f 1 2 3 4 5))))
      (if (not (equal? y 15)) (display "unit-test: test 8.6.2 failing\n")))
    (let ((y (new-eval '(f 1 2 3 4))))
      (if (not (equal? y 10)) (display "unit-test: test 8.6.3 failing\n")))
    (let ((y (new-eval '(f 1 2 3))))
      (if (not (equal? y 6)) (display "unit-test: test 8.6.4 failing\n")))
    ((global-env 'delete!) 'f))


  ; analyze
  (let ((x ((analyze '(lambda () (+ 3 5))) global-env)))
    ((global-env 'define!) 'f x)
    (let ((y ((analyze '(f)) global-env)))
      (if (not (equal? y 8)) (display "unit-test: test 8.7 failing\n")))
    ((global-env 'delete!) 'f))
  (let ((x ((analyze '(lambda (x) (* 3 x))) global-env)))
    ((global-env 'define!) 'f x)
    (let ((y ((analyze '(f 5)) global-env)))
      (if (not (equal? y 15)) (display "unit-test: test 8.8 failing\n")))
    ((global-env 'delete!) 'f))
  (let ((x ((analyze '(lambda (x y) (+ x y))) global-env)))
    ((global-env 'define!) 'f x)
    (let ((y ((analyze '(f 3 4)) global-env)))
      (if (not (equal? y 7)) (display "unit-test: test 8.9 failing\n")))
    ((global-env 'delete!) 'f))
  (let ((plus5 ((analyze '(lambda (x) (+ x y))) ((global-env 'extended)'(y)'(5)))))
    ((global-env 'define!) 'f plus5)
    (let ((y ((analyze '(f 6)) global-env)))
      (if (not (equal? y 11)) (display "unit-test: test 8.10 failing\n")))
    ((global-env 'delete!) 'f))
  (let ((x ((analyze '((lambda () 45))) global-env)))
    (if (not (equal? x 45)) (display "unit-test: test 8.11 failing\n")))
  (let ((x ((analyze '((lambda (x) (+ x 7)) 5)) global-env)))
    (if (not (equal? x 12)) (display "unit-test: test 8.12 failing\n")))
  (let ((x ((analyze '(let ((x 5)) ((lambda (u v) (+ u v)) x 6))) global-env)))
    (if (not (equal? x 11)) (display "unit-test: test 8.13 failing\n")))
  (let ((x ((analyze '(lambda arg (apply + arg))) global-env)))
    ((global-env 'define!) 'f x)
    (let ((y ((analyze '(f 1 2 3 4 5)) global-env)))
      (if (not (equal? y 15)) (display "unit-test: test 8.14 failing\n")))
    ((global-env 'delete!) 'f))
  (let ((x ((analyze '(lambda (x y z . t) (+ x y z (apply + t)))) global-env)))
    ((global-env 'define!) 'f x)
    (let ((y ((analyze '(f 1 2 3 4 5)) global-env)))
      (if (not (equal? y 15)) (display "unit-test: test 8.15 failing\n")))
    (let ((y ((analyze '(f 1 2 3 4)) global-env)))
      (if (not (equal? y 10)) (display "unit-test: test 8.16 failing\n")))
    (let ((y ((analyze '(f 1 2 3)) global-env)))
      (if (not (equal? y 6)) (display "unit-test: test 8.17 failing\n")))
    ((global-env 'delete!) 'f))
  ;
  ; begin
  (display "testing begin expressions...\n")
  ;
  (let ((x (new-eval '(begin 1 2 3 4))))
    (if (not (equal? x 4)) (display "unit-test: test 9.0 failing\n")))
  ;
  (let ((x ((analyze '(begin 1 2 3 4)) global-env)))
    (if (not (equal? x 4)) (display "unit-test: test 9.1 failing\n")))
  ;
  ;cond
  ;
  ; eval
  (let ((x (new-eval '(cond (#t 0) (#f 1) (#f 2) (else 3)))))
    (if (not (equal? x 0)) (display "unit-test: test 10.0 failing\n")))
  (let ((x (new-eval '(cond (#f 0) (#t 1) (#f 2) (else 3)))))
    (if (not (equal? x 1)) (display "unit-test: test 10.1 failing\n")))
  (let ((x (new-eval '(cond (#f 0) (#f 1) (#t 2) (else 3)))))
    (if (not (equal? x 2)) (display "unit-test: test 10.2 failing\n")))
  (let ((x (new-eval '(cond (#f 0) (#f 1) (#f 2) (else 3)))))
    (if (not (equal? x 3)) (display "unit-test: test 10.3 failing\n")))
  (let ((x (new-eval '(cond (#f 0) (else 4)))))
    (if (not (equal? x 4)) (display "unit-test: test 10.4 failing\n")))
  (let ((x (new-eval '(cond (else 5)))))
    (if (not (equal? x 5)) (display "unit-test: test 10.5 failing\n")))

  ; analyze
  (let ((x ((analyze '(cond (#t 0) (#f 1) (#f 2) (else 3))) global-env)))
    (if (not (equal? x 0)) (display "unit-test: test 10.6 failing\n")))
  (let ((x ((analyze '(cond (#f 0) (#t 1) (#f 2) (else 3))) global-env)))
    (if (not (equal? x 1)) (display "unit-test: test 10.7 failing\n")))
  (let ((x ((analyze '(cond (#f 0) (#f 1) (#t 2) (else 3))) global-env)))
    (if (not (equal? x 2)) (display "unit-test: test 10.8 failing\n")))
  (let ((x ((analyze '(cond (#f 0) (#f 1) (#f 2) (else 3))) global-env)))
    (if (not (equal? x 3)) (display "unit-test: test 10.9 failing\n")))
  (let ((x ((analyze '(cond (#f 0) (else 4))) global-env)))
    (if (not (equal? x 4)) (display "unit-test: test 10.10 failing\n")))
  (let ((x ((analyze '(cond (else 5))) global-env)))
    (if (not (equal? x 5)) (display "unit-test: test 10.11 failing\n")))
  ;
  ; or
  (display "testing or expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(or #t nonsense1 nonsense2))))
    (if (not (equal? x #t)) (display "unit-test: test 11.0 failing\n")))
  (let ((x (new-eval '(or #f #t nonsense))))
    (if (not (equal? x #t)) (display "unit-test: test 11.1 failing\n")))
  (let ((x (new-eval '(or #f #f #t))))
    (if (not (equal? x #t)) (display "unit-test: test 11.2 failing\n")))
  (let ((x (new-eval '(or #f #f #f))))
    (if (not (equal? x #f)) (display "unit-test: test 11.3 failing\n")))
  (let ((x (new-eval '(or))))
    (if (not (equal? x #f)) (display "unit-test: test 11.4 failing\n")))
  (let ((x (new-eval '(or #t))))
    (if (not (equal? x #t)) (display "unit-test: test 11.5 failing\n")))
  (let ((x (new-eval '(or #f))))
    (if (not (equal? x #f)) (display "unit-test: test 11.6 failing\n")))

  ; analyze
  (let ((x ((analyze '(or #t nonsense1 nonsense2)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 11.7 failing\n")))
  (let ((x ((analyze '(or #f #t nonsense)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 11.8 failing\n")))
  (let ((x ((analyze '(or #f #f #t)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 11.9 failing\n")))
  (let ((x ((analyze '(or #f #f #f)) global-env)))
    (if (not (equal? x #f)) (display "unit-test: test 11.10 failing\n")))
  (let ((x ((analyze '(or)) global-env)))
    (if (not (equal? x #f)) (display "unit-test: test 11.11 failing\n")))
  (let ((x ((analyze '(or #t)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 11.12 failing\n")))
  (let ((x ((analyze '(or #f)) global-env)))
    (if (not (equal? x #f)) (display "unit-test: test 11.13 failing\n")))
  ;
  ; and
  (display "testing and expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(and #f nonsense1 nonsense2))))
    (if (not (equal? x #f)) (display "unit-test: test 12.0 failing\n")))
  (let ((x (new-eval '(and #t #f nonsense))))
    (if (not (equal? x #f)) (display "unit-test: test 12.1 failing\n")))
  (let ((x (new-eval '(and #t #t #f))))
    (if (not (equal? x #f)) (display "unit-test: test 12.2 failing\n")))
  (let ((x (new-eval '(and #t #t #t))))
    (if (not (equal? x #t)) (display "unit-test: test 12.3 failing\n")))
  (let ((x (new-eval '(and))))
    (if (not (equal? x #t)) (display "unit-test: test 12.4 failing\n")))
  (let ((x (new-eval '(and #t))))
    (if (not (equal? x #t)) (display "unit-test: test 12.5 failing\n")))
  (let ((x (new-eval '(and #f))))
    (if (not (equal? x #f)) (display "unit-test: test 12.6 failing\n")))

  ; analyze
  (let ((x ((analyze '(and #f nonsense1 nonsense2)) global-env)))
    (if (not (equal? x #f)) (display "unit-test: test 12.7 failing\n")))
  (let ((x ((analyze '(and #t #f nonsense)) global-env)))
    (if (not (equal? x #f)) (display "unit-test: test 12.8 failing\n")))
  (let ((x ((analyze '(and #t #t #f)) global-env)))
    (if (not (equal? x #f)) (display "unit-test: test 12.9 failing\n")))
  (let ((x ((analyze '(and #t #t #t)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 12.10 failing\n")))
  (let ((x ((analyze '(and)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 12.11 failing\n")))
  (let ((x ((analyze '(and #t)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 12.12 failing\n")))
  (let ((x ((analyze '(and #f)) global-env)))
    (if (not (equal? x #f)) (display "unit-test: test 12.13 failing\n")))
  ;
  ; let
  (display "testing let expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(let ((x 5)) (+ x 7)))))
    (if (not (equal? x 12)) (display "unit-test: test 13.0 failing\n")))
  (let ((x (new-eval '(let ((x 5) (y 3)) (+ x y)))))
    (if (not (equal? x 8)) (display "unit-test: test 13.1 failing\n")))
  (let ((x (new-eval '(let ((x 5)(y 6)) (let ((z 7)) (+ x y z))))))
    (if (not (equal? x 18)) (display "unit-test: test 13.2 failing\n")))
  (let ((x (new-eval '(let ((x 5)(y 6)) (let ((z 7) (x 10)) (+ x y z))))))
    (if (not (equal? x 23)) (display "unit-test: test 13.3 failing\n")))
  (let ((x (new-eval '(let ((x 1)) (let ((y 2)) (let ((z 3)) (+ x y z)))))))
    (if (not (equal? x 6)) (display "unit-test: test 13.4 failing\n")))

  ; analyze
  (let ((x ((analyze '(let ((x 5)) (+ x 7))) global-env)))
    (if (not (equal? x 12)) (display "unit-test: test 13.5 failing\n")))
  (let ((x ((analyze '(let ((x 5) (y 3)) (+ x y))) global-env)))
    (if (not (equal? x 8)) (display "unit-test: test 13.6 failing\n")))
  (let ((x ((analyze '(let ((x 5)(y 6)) (let ((z 7)) (+ x y z)))) global-env)))
    (if (not (equal? x 18)) (display "unit-test: test 13.7 failing\n")))
  (let ((x ((analyze '(let ((x 5)(y 6)) (let ((z 7) (x 10)) (+ x y z)))) 
            global-env)))
    (if (not (equal? x 23)) (display "unit-test: test 13.8 failing\n")))
  (let ((x ((analyze '(let ((x 1)) (let ((y 2)) (let ((z 3)) (+ x y z))))) 
            global-env)))
    (if (not (equal? x 6)) (display "unit-test: test 13.9 failing\n")))
  ;
  ; named-let
  (display "testing named let expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(let loop ((i 5) (acc 1)) 
                     (if (equal? 1 i) acc (loop (- i 1) (* i acc)))))))
    (if (not (equal? x 120)) (display "unit-test: unit 14.0 failing\n")))

  ; analyze
  (let ((x ((analyze '(let loop ((i 5) (acc 1)) 
                     (if (equal? 1 i) acc (loop (- i 1) (* i acc))))) global-env)))
    (if (not (equal? x 120)) (display "unit-test: unit 14.1 failing\n")))
  ;
  ; let*
  (display "testing let* expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(let* ((x 5)(y (+ x 2))) (+ x y)))))
    (if (not (equal? x 12)) (display "unit-test: test 15.0 failing\n")))

  ; analyze
  (let ((x ((analyze '(let* ((x 5)(y (+ x 2))) (+ x y))) global-env)))
    (if (not (equal? x 12)) (display "unit-test: test 15.1 failing\n")))
  ;
  ; letrec
  (display "testing recursive let expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(letrec 
                    ((loop (lambda (n) (if (= 0 n) 1 (* n (loop (- n 1)))))))
                    (loop 5)))))
    (if (not (equal? x 120)) (display "unit-test: test 15.2 failing\n")))

  ; analyze
  (let ((x ((analyze '(letrec 
                     ((loop (lambda (n) (if (= 0 n) 1 (* n (loop (- n 1)))))))
                     (loop 5))) global-env)))
    (if (not (equal? x 120)) (display "unit-test: test 15.3 failing\n")))
  ;
  ; application
  (display "testing application expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(+))))
    (if (not (equal? x 0)) (display "unit-test: test 16.0 failing\n")))
  (let ((x (new-eval '(+ 2))))
    (if (not (equal? x 2)) (display "unit-test: test 16.1 failing\n")))
  (let ((x (new-eval '(+ 2 4))))
    (if (not (equal? x 6)) (display "unit-test: test 16.2 failing\n")))
  (let ((x (new-eval '(car '(1 2)))))
    (if (not (equal? x 1)) (display "unit-test: test 16.3 failing\n")))
  (let ((x (new-eval '(cdr '(1 2)))))
    (if (not (equal? x (list 2))) (display "unit-test: test 16.4 failing\n")))
  (let ((x (new-eval '(cons 2 '()))))
    (if (not (equal? x (list 2))) (display "unit-test: test 16.5 failing\n")))
  (let ((x (new-eval '(cons 5 (cons 2 '())))))
    (if (not (equal? x (list 5 2))) (display "unit-test: test 16.6 failing\n")))
  (let ((x (new-eval '(eval (+ 1 2)))))
    (if (not (equal? x 3)) (display "unit-test:test 16.7 failing\n")))

  ; analyze
  (let ((x ((analyze '(+)) global-env)))
    (if (not (equal? x 0)) (display "unit-test: test 16.8 failing\n")))
  (let ((x ((analyze '(+ 2)) global-env)))
    (if (not (equal? x 2)) (display "unit-test: test 16.9 failing\n")))
  (let ((x ((analyze '(+ 2 4)) global-env)))
    (if (not (equal? x 6)) (display "unit-test: test 16.10 failing\n")))
  (let ((x ((analyze '(car '(1 2))) global-env)))
    (if (not (equal? x 1)) (display "unit-test: test 16.11 failing\n")))
  (let ((x ((analyze '(cdr '(1 2))) global-env)))
    (if (not (equal? x (list 2))) (display "unit-test: test 16.12 failing\n")))
  (let ((x ((analyze '(cons 2 '())) global-env)))
    (if (not (equal? x (list 2))) (display "unit-test: test 16.13 failing\n")))
  (let ((x ((analyze '(cons 5 (cons 2 '()))) global-env)))
    (if (not (equal? x (list 5 2))) (display "unit-test: test 16.14 failing\n")))
  (let ((x ((analyze '(eval (+ 1 2))) global-env)))
    (if (not (equal? x 3)) (display "unit-test:test 16.15 failing\n")))
  ;
  ; defined?
  (display "testing defined? expressions...\n")
  ;
  ; eval
  (let ((x (new-eval '(defined? +))))
    (if (not (equal? x #t)) (display "unit-test: test 17.0 failing\n")))
  (let ((x (new-eval '(defined? car))))
    (if (not (equal? x #t)) (display "unit-test: test 17.1 failing\n")))
  (let ((x (new-eval '(defined? cdr))))
    (if (not (equal? x #t)) (display "unit-test: test 17.2 failing\n")))
  (let ((x (new-eval '(defined? some-random-name))))
    (if (not (equal? x #f)) (display "unit-test: test 17.3 failing\n")))
  (let ((x (new-eval '(defined? (this is not even a name)))))
    (if (not (equal? x #f)) (display "unit-test: test 17.4 failing\n")))

  ; analyze
  (let ((x ((analyze '(defined? +)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 17.5 failing\n")))
  (let ((x ((analyze '(defined? car)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 17.6 failing\n")))
  (let ((x ((analyze '(defined? cdr)) global-env)))
    (if (not (equal? x #t)) (display "unit-test: test 17.7 failing\n")))
  (let ((x ((analyze '(defined? some-random-name)) global-env)))
    (if (not (equal? x #f)) (display "unit-test: test 17.8 failing\n")))
  (let ((x ((analyze '(defined? (this is not even a name))) global-env)))
    (if (not (equal? x #f)) (display "unit-test: test 17.9 failing\n")))

  ; thunk
  (display "testing thunk ...\n")

  (let ((t1 (thunk '(+ 1 1) global-env)))
    (if (not (equal? (force-thunk t1) 2)) 
      (display "unit-test: test 19.1 failing\n"))
    (if (not (equal? (force-thunk t1) 2)) 
      (display "unit-test: test 19.2 failing\n"))
    (if (not (equal? (force-thunk t1) 2)) 
      (display "unit-test: test 19.3 failing\n"))
    (if (not (equal? (force-thunk t1) 2)) 
      (display "unit-test: test 19.4 failing\n"))
    (if (not (thunk? t1)) (display "unit-test: test 19.5 failing\n"))
    (if (thunk? 0) (display "unit-test: test 19.6 failing\n"))
    (if (thunk? #\a) (display "unit-test: test 19.7 failing\n"))
    (if (thunk? "a") (display "unit-test: test 19.8 failing\n"))
    (if (thunk? #t) (display "unit-test: test 19.9 failing\n"))
    (if (thunk? #f) (display "unit-test: test 19.10 failing\n"))
  )
 
  ; load
  (display "testing loading files ...\n") 

  ; eval
  (let ((s (new-eval '(load "test-files.scm"))))
    (if (not (equal? s " test-files.scm loaded"))
      (display "unit-test: test 18.0 failing\n")))

  (set! global-env (setup-environment)) ; clears include guards

  ; analyze
  (let ((s (analyze '(load "test-files.scm"))))
    (let ((t (s global-env)))
      (if (not (equal? t " test-files.scm loaded"))
        (display "unit-test: test 18.1 failing\n"))))

  (display "unit-test: test complete\n"))

(unit-test)
(exit 0)
