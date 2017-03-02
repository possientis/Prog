(load "main.scm")
(load "tools.scm")

(set-debug #f)

(define (unit-test)
  ;
  (newline)
  (display "unit-test: starting test\n")
  ;
  ; self-evaluating
  (display "testing self-evaluating expressions...\n")
  (test-expression '3 3 "self-evaluating.1")
  (test-expression '3.5 3.5 "self-evaluating.2")
  (test-expression '"hello" "hello" "self-evaluating.3")
  (test-expression '"hello\n" "hello\n" "self-evaluating.4")
  (test-expression '#\a #\a "self-evaluating.5")
  (test-expression '#t #t "self-evaluating.6")
  (test-expression '#f #f "self-evaluating.7")
  ;
  ; variable
  (display "testing variable expressions...\n")
  (test-expression '+ (make-primitive-procedure +) "variable.1")
  (test-expression '* (make-primitive-procedure *) "variable.2")
  (test-expression '- (make-primitive-procedure -) "variable.3")
  (test-expression '/ (make-primitive-procedure /) "variable.4")
  (test-expression '= (make-primitive-procedure =) "variable.5")
  (test-expression '< (make-primitive-procedure <) "variable.6")
  (test-expression '> (make-primitive-procedure >) "variable.7")
  (test-expression '<= (make-primitive-procedure <=) "variable.8")
  (test-expression '>= (make-primitive-procedure >=) "variable.9")
  (test-expression 'append (make-primitive-procedure append) "variable.10")
  (test-expression 'boolean? (make-primitive-procedure boolean?) "variable.12")
  (test-expression 'caadr (make-primitive-procedure caadr) "variable.13")
  (test-expression 'caar (make-primitive-procedure caar) "variable.14")
  (test-expression 'cadddr (make-primitive-procedure cadddr) "variable.15")
  (test-expression 'caddr (make-primitive-procedure caddr) "variable.16")
  (test-expression 'cadr (make-primitive-procedure cadr) "variable.17")
  (test-expression 'car (make-primitive-procedure car) "variable.18")
  (test-expression 'cdadr (make-primitive-procedure cdadr) "variable.19")
  (test-expression 'cdar (make-primitive-procedure cdar) "variable.20")
  (test-expression 'cdr (make-primitive-procedure cdr) "variable.21")
  (test-expression 'cdddr (make-primitive-procedure cdddr) "variable.22")
  (test-expression 'cddr (make-primitive-procedure cddr) "variable.23")
  (test-expression 'char? (make-primitive-procedure char?) "variable.24")
  (test-expression 'close-port(make-primitive-procedure close-port) "variable.25")
  (test-expression 'cons (make-primitive-procedure cons) "variable.26")
  (test-expression 'display (make-primitive-procedure new-display) "variable.27")

  (test-expression 
    'eof-object? (make-primitive-procedure eof-object?) "variable.28")

  (test-expression 'eq? (make-primitive-procedure eq?) "variable.29")
  (test-expression 'equal? (make-primitive-procedure equal?) "variable.30")
  (test-expression 'error (make-primitive-procedure error) "variable.31")
  (test-expression 'exit (make-primitive-procedure exit) "variable.33")
  (test-expression 'hash (make-primitive-procedure hash) "variable.34")

  (test-expression 
    'inexact->exact (make-primitive-procedure inexact->exact) "variable.35")

  (test-expression 'length (make-primitive-procedure length) "variable.36")
  (test-expression 'list (make-primitive-procedure list) "variable.37")

  (test-expression 
    'make-vector (make-primitive-procedure make-vector) "variable.39")

  (test-expression 'modulo (make-primitive-procedure modulo) "variable.41")
  (test-expression 'newline (make-primitive-procedure newline) "variable.42")
  (test-expression 'null? (make-primitive-procedure null?) "variable.43")
  (test-expression 'number? (make-primitive-procedure number?) "variable.44")

  (test-expression 
    'number->string (make-primitive-procedure number->string) "variable.45")

  (test-expression 
    'object->string (make-primitive-procedure new-object->string) "variable.46")

  (test-expression 'open-file (make-primitive-procedure open-file) "variable.47")
  (test-expression 'pair? (make-primitive-procedure pair?) "variable.48")
  (test-expression 'read (make-primitive-procedure read) "variable.49")
  (test-expression 'require (make-primitive-procedure new-require) "variable.50")
  (test-expression 'reverse (make-primitive-procedure reverse) "variable.51")
  (test-expression 'set-car! (make-primitive-procedure set-car!) "variable.52")
  (test-expression 'set-cdr! (make-primitive-procedure set-cdr!) "variable.53")
  (test-expression 'string? (make-primitive-procedure string?) "variable.54")

  (test-expression 
    'string-append (make-primitive-procedure string-append) "variable.55")

  (test-expression 'symbol? (make-primitive-procedure symbol?) "variable.56")

  (test-expression 
    'vector-fill! (make-primitive-procedure vector-fill!) "variable.57")
  
  (test-expression 
    'vector-length (make-primitive-procedure vector-length) "variable.58")

  (test-expression 
    'vector-ref (make-primitive-procedure vector-ref) "variable.59")

  (test-expression 
    'vector-set!(make-primitive-procedure vector-set!)"variable.60")
  ;
  ; quoted
  (display "testing quoted expressions...\n") 
  ; the value of expression (quote hello) is (the symbol) hello
  (test-expression '(quote hello) 'hello "quoted.1")
  (test-expression (quote (quote hello))  (quote hello) "quoted.2")
  (test-expression (quote (quote hello)) 'hello "quoted.3")
  (test-expression (quote 'hello) 'hello "quoted.4")
  (test-expression ''hello 'hello "quoted.5")
  ; the value of expression (quote 3) is the integer 3
  (test-expression '(quote 3) 3 "quoted.6")
  (test-expression ''3 3 "quoted.7")
  ; the value of expression (quote 3.5) is the floating number 3.5
  (test-expression '(quote 3.5) 3.5 "quoted.8")
  (test-expression ''3.5 3.5 "quoted.9")
  ; the value of expression (quote #\a) is the character #\a
  (test-expression '(quote #\a) #\a "quoted.10")
  (test-expression ''#\a #\a "quoted.11")
  ; the value of expression (quote "hello") is the string "hello"
  (test-expression '(quote "hello") "hello" "quoted.11")
  (test-expression ''"hello" "hello" "quoted.12")
  ; the value of expression (quote #t) is the boolean value #t
  (test-expression '(quote #t) #t "quoted.13")
  (test-expression ''#t #t "quoted.14")
  ; the value of expression (quote #f) is the boolean value #f
  (test-expression '(quote #f) #f "quoted.15")
  (test-expression ''#f #f "quoted.16")
  ; the value of expression (quote (list 3)) is the expression (list 3)
  (test-expression '(quote (list 3)) '(list 3) "quoted.17")
  (test-expression ''(list 3) '(list 3) "quoted.18")
  (test-expression ''(list 3) (list 'list 3) "quoted.19")
  ; while the value of expression (list 3) is the value (list 3)
  (test-expression '(list 3) (list 3) "quoted.20")
  (test-expression '(list 3) '(3) "quoted.21")
  ; the value of expression (quote (list cons "abc" #\a)) is the expression
  ; (list cons "abc" #\a) which is not the same as the value (list cons "abc" #\a)
  (test-expression '(quote(list cons "abc" #\a)) '(list cons "abc" #\a)"quoted.22")
  (test-expression ''(list cons "abc" #\a) '(list cons "abc" #\a) "quoted.23")
  (test-expression ''(list cons "abc" #\a)(list 'list 'cons "abc" #\a)"quoted.24")
  ; the value (list cons "abc" #a) is the value of expression (list cons "abc" #\a)
  ; which is a list of three elements, where the first element is a value (an 
  ; object) representing the primitive operator 'cons'
  (test-expression '(list cons "abc" #\a) 
                   (list (make-primitive-procedure cons) "abc" #\a) "quoted.25")
  ; the value of the expression (quote (length (2 3))) is the expression 
  ; (length (2 3)). However, the expression (length (2 3)) cannot be evaluated
  ; as the expression (2 3) cannot be evaluated since 2 is not a valid operator
  (test-expression '(quote (length (2 3))) '(length (2 3)) "quoted.26")
  (test-expression '(quote (length (2 3))) (list 'length (list 2 3)) "quoted.27")
  ; the value of expression (quote (2 3)) is expression (2 3)
  (test-expression '(quote (2 3)) '(2 3) "quoted.28")
  (test-expression '(quote (2 3)) (list 2 3) "quoted.29")
  ; so the value of expression '(2 3) is the expression (2 3) 
  (test-expression ''(2 3) '(2 3) "quoted.30")
  (test-expression ''(2 3) (list 2 3) "quoted.31")
  ; the value of expression '(quote (length '(2 3))) is expression (length '(2 3))
  (test-expression '(quote (length '(2 3))) '(length '(2 3)) "quoted.32")
  (test-expression ''(length '(2 3)) '(length '(2 3)) "quoted.33")
  (test-expression ''(length (quote (2 3))) '(length '(2 3)) "quoted.34")
  (test-expression ''(length '(2 3)) '(length (quote (2 3))) "quoted.35")
  (test-expression 
    ''(length '(2 3)) (list 'length (list 'quote (list 2 3))) "quoted.36")
  ;
  ; assignment
  (display "testing assignment expressions...\n")
  (let ((env ((global-env 'extended) 'var #f)))    ; extended env with var = #f
    (test-expression 'var #f "assignment.1" env)    
    ; strict assignment
    (let ((result (strict-eval '(set! var #t) env)))
      (assert-equals result unspecified-value "assignment.2")
      (test-expression 'var #t "assignment.3" env))     ; testing outcome 
    ; lazy assignment : cannot use test-expression (need 'test-forced-expression')
    (let ((result (lazy-eval '(set! var #\a) env))) 
      (assert-equals (force-thunk result) unspecified-value "assignment.4")
      (test-forced-expression 'var #\a "assignment.5" env))
    ; analyzed assignment
    (let ((result (analyze-eval '(set! var 45) env)))
      (assert-equals result unspecified-value "assignment.6")
      (test-expression 'var 45 "assignment.7" env)))    
  ;
  ; definition
  (display "testing definition expressions...\n")
  (let ((env ((global-env 'extended) 'var #f)))
    (test-expression 'var #f "definition.1" env)
    (assert-equals ((env 'defined?) 'var) #t "definition.2")
    (assert-equals ((global-env 'defined?) 'var) #f "definition.3")
    ((env 'delete!) 'var)
    (assert-equals ((env 'defined?) 'var) #f "definition.4")
    (assert-equals ((global-env 'defined?) 'var) #f "definition.5")
    ; strict definition
    (let ((result (strict-eval '(define var 12) env)))
      (assert-equals result unspecified-value "definiton.6")
      (assert-equals ((env 'defined?) 'var) #t "definition.7")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.8")
      (test-expression 'var 12 "definition.9" env)
      ((env 'delete!) 'var)
      (assert-equals ((env 'defined?) 'var) #f "definition.10")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.11"))
    ; lazy definition (cannot use 'test-expression', need 'test-forced-expression')
    (let ((result (lazy-eval '(define var 0.3) env)))
      (assert-equals (force-thunk result) unspecified-value "definiton.12")
      (assert-equals ((env 'defined?) 'var) #t "definition.13")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.14")
      (test-forced-expression 'var 0.3 "definition.15" env)
      ((env 'delete!) 'var)
      (assert-equals ((env 'defined?) 'var) #f "definition.21")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.22"))
    ; analyze definition
    (let ((result (analyze-eval '(define var "hello") env)))
      (assert-equals result unspecified-value "definiton.23")
      (assert-equals ((env 'defined?) 'var) #t "definition.24")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.25")
      (test-expression 'var "hello" "definition.26" env)
      ((env 'delete!) 'var)
      (assert-equals ((env 'defined?) 'var) #f "definition.27")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.28"))
    ; strict definition: function with no argument
    (let ((result (strict-eval '(define (f) 12) env)))
      (assert-equals result unspecified-value "definiton.52")
      (assert-equals ((env 'defined?) 'f) #t "definition.53")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.54")
      (test-expression '(f) 12 "definition.55" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.56")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.57"))
    ; lazy definition: function with no argument (test-expression works !!)
    (let ((result (lazy-eval '(define (f) 0.3) env)))
      (assert-equals (force-thunk result) unspecified-value "definiton.58")
      (assert-equals ((env 'defined?) 'f) #t "definition.59")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.60")
      (test-expression '(f) 0.3 "definition 61" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.62")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.63"))
    ; analyze definition: function with no argument
    (let ((result (analyze-eval '(define (f) "hello") env)))
      (assert-equals result unspecified-value "definiton.64")
      (assert-equals ((env 'defined?) 'f) #t "definition.65")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.66")
      (test-expression '(f) "hello" "definition.67" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.68")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.69"))
    ; strict definition: function with a single argument
    (let ((result (strict-eval '(define (f x) (* x x)) env)))
      (assert-equals result unspecified-value "definiton.87")
      (assert-equals ((env 'defined?) 'f) #t "definition.88")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.89")
      (test-expression '(f 5) 25 "definition.90" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.91")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.92"))
    ; lazy definition: function with a single argument (test-expression works !!)
    (let ((result (lazy-eval '(define (f x) (* x x x)) env)))
      (assert-equals (force-thunk result) unspecified-value "definiton.93")
      (assert-equals ((env 'defined?) 'f) #t "definition.94")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.95")
      (test-expression '(f 3) 27 "definition.96" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.97")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.98"))
    ; analyze definition: function with a single argument
    (let ((result (analyze-eval '(define (f x) (+ x x x)) env)))
      (assert-equals result unspecified-value "definiton.99")
      (assert-equals ((env 'defined?) 'f) #t "definition.100")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.101")
      (test-expression '(f 6) 18 "definition.102" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.103")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.104"))
    ; strict definition: function with two arguments
    (let ((result (strict-eval '(define (f x y) (+ x y)) env)))
      (assert-equals result unspecified-value "definiton.122")
      (assert-equals ((env 'defined?) 'f) #t "definition.123")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.124")
      (test-expression '(f 5 7) 12 "definition.125" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.126")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.127"))
    ; lazy definition: function with two arguments (test-expression works !!)
    (let ((result (lazy-eval '(define (f x y) (* x y)) env)))
      (assert-equals (force-thunk result) unspecified-value "definiton.128")
      (assert-equals ((env 'defined?) 'f) #t "definition.129")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.130")
      (test-expression '(f 3 5) 15 "definition.131" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.132")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.133"))
    ; analyze definition: function with two arguments
    (let ((result (analyze-eval '(define (f a b) (+ a b 7)) env)))
      (assert-equals result unspecified-value "definiton.134")
      (assert-equals ((env 'defined?) 'f) #t "definition.135")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.136")
      (test-expression '(f 6 10) 23 "definition.137" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.138")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.139"))
    ; strict definition: function with optional arguments
    (let ((result (strict-eval '(define (f . args) args) env)))
      (assert-equals result unspecified-value "definiton.158")
      (assert-equals ((env 'defined?) 'f) #t "definition.159")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.160")
      (test-expression '(f) '() "definition.161" env)
      ; we cannot test directly that '(f 0) evaluates to '(0) because
      ; this may not be the case with lazy evaluation. We need to force
      ; successive layers of the list, which may be a list of thunks.
      (test-expression '(car (f 0)) 0  "definition.162" env)
      (test-expression '(cdr (f 0)) '() "definition.163" env)
      (test-expression '(car (f 2 3)) 2  "definition.164" env)
      (test-expression '(cadr (f 2 3)) 3  "definition.165" env)
      (test-expression '(cddr (f 2 3)) '() "definition.166" env)
      (test-expression '(car (f 4 5 6)) 4  "definition.167" env)
      (test-expression '(cadr (f 4 5 6)) 5  "definition.168" env)
      (test-expression '(caddr (f 4 5 6)) 6  "definition.169" env)
      (test-expression '(cdddr (f 4 5 6)) '() "definition.170" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.171")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.172"))
    ; lazy definition: function with optional arguments
    (let ((result (lazy-eval '(define (f . args) args) env)))
      (assert-equals (force-thunk result) unspecified-value "definiton.173")
      (assert-equals ((env 'defined?) 'f) #t "definition.174")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.175")
      (test-expression '(f) '() "definition.176" env)
      (test-expression '(car (f 0)) 0  "definition.177" env)
      (test-expression '(cdr (f 0)) '() "definition.178" env)
      (test-expression '(car (f 2 3)) 2  "definition.179" env)
      (test-expression '(cadr (f 2 3)) 3  "definition.180" env)
      (test-expression '(cddr (f 2 3)) '() "definition.181" env)
      (test-expression '(car (f 4 5 6)) 4  "definition.182" env)
      (test-expression '(cadr (f 4 5 6)) 5  "definition.183" env)
      (test-expression '(caddr (f 4 5 6)) 6  "definition.184" env)
      (test-expression '(cdddr (f 4 5 6)) '() "definition.185" env)
       ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.186")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.187"))
    ; analyze definition: function with optional arguments
    (let ((result (analyze-eval '(define (f . args) args) env)))
      (assert-equals result unspecified-value "definiton.188")
      (assert-equals ((env 'defined?) 'f) #t "definition.189")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.190")
      (test-expression '(f) '() "definition.191" env)
      (test-expression '(car (f 0)) 0  "definition.192" env)
      (test-expression '(cdr (f 0)) '() "definition.193" env)
      (test-expression '(car (f 2 3)) 2  "definition.194" env)
      (test-expression '(cadr (f 2 3)) 3  "definition.195" env)
      (test-expression '(cddr (f 2 3)) '() "definition.196" env)
      (test-expression '(car (f 4 5 6)) 4  "definition.197" env)
      (test-expression '(cadr (f 4 5 6)) 5  "definition.198" env)
      (test-expression '(caddr (f 4 5 6)) 6  "definition.199" env)
      (test-expression '(cdddr (f 4 5 6)) '() "definition.200" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.201")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.202"))
    ; strict definition: function with optional arguments + 1 required
    (let ((result (strict-eval '(define (f x . args) (cons x args)) env)))
      (assert-equals result unspecified-value "definiton.246")
      (assert-equals ((env 'defined?) 'f) #t "definition.247")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.248")
      ; we cannot test directly that '(f 0) evaluates to '(0) because
      ; this may not be the case with lazy evaluation. We need to force
      ; successive layers of the list, which may be a list of thunks.
      (test-expression '(car (f 0)) 0  "definition.249" env)
      (test-expression '(cdr (f 0)) '() "definition.250" env)
      (test-expression '(car (f 2 3)) 2  "definition.251" env)
      (test-expression '(cadr (f 2 3)) 3  "definition.252" env)
      (test-expression '(cddr (f 2 3)) '() "definition.253" env)
      (test-expression '(car (f 4 5 6)) 4  "definition.254" env)
      (test-expression '(cadr (f 4 5 6)) 5  "definition.255" env)
      (test-expression '(caddr (f 4 5 6)) 6  "definition.256" env)
      (test-expression '(cdddr (f 4 5 6)) '() "definition.257" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.258")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.259"))
    ; lazy definition: function with optional arguments + 1 required
    (let ((result (lazy-eval '(define (f x . args) (cons x args)) env)))
      (assert-equals (force-thunk result) unspecified-value "definiton.260")
      (assert-equals ((env 'defined?) 'f) #t "definition.261")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.262")
      (test-expression '(car (f 0)) 0  "definition.263" env)
      (test-expression '(cdr (f 0)) '() "definition.264" env)
      (test-expression '(car (f 2 3)) 2  "definition.265" env)
      (test-expression '(cadr (f 2 3)) 3  "definition.266" env)
      (test-expression '(cddr (f 2 3)) '() "definition.267" env)
      (test-expression '(car (f 4 5 6)) 4  "definition.268" env)
      (test-expression '(cadr (f 4 5 6)) 5  "definition.269" env)
      (test-expression '(caddr (f 4 5 6)) 6  "definition.270" env)
      (test-expression '(cdddr (f 4 5 6)) '() "definition.271" env)
       ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.272")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.273"))
    ; analyze definition: function with optional arguments + 1 required
    (let ((result (analyze-eval '(define (f x . args) (cons x args)) env)))
      (assert-equals result unspecified-value "definiton.274")
      (assert-equals ((env 'defined?) 'f) #t "definition.275")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.276")
      (test-expression '(car (f 0)) 0  "definition.277" env)
      (test-expression '(cdr (f 0)) '() "definition.278" env)
      (test-expression '(car (f 2 3)) 2  "definition.279" env)
      (test-expression '(cadr (f 2 3)) 3  "definition.280" env)
      (test-expression '(cddr (f 2 3)) '() "definition.281" env)
      (test-expression '(car (f 4 5 6)) 4  "definition.282" env)
      (test-expression '(cadr (f 4 5 6)) 5  "definition.283" env)
      (test-expression '(caddr (f 4 5 6)) 6  "definition.284" env)
      (test-expression '(cdddr (f 4 5 6)) '() "definition.285" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.286")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.287")))

  ; if
  (display "testing if expressions...\n")
  (test-expression '(if #t "yes" "no") "yes" "if.1") 
  (test-expression '(if #f "yes" "no") "no" "if.2") 
  (test-expression '(if #t "yes") "yes" "if.3") 
  (test-expression '(if (equal? 3 3) (+ 2 3) (* 4 5)) 5 "if.4")
  (test-expression '(if (equal? 3 4) (+ 2 3) (* 4 5)) 20 "if.5")
  (test-expression '(if #t 0 (error "should not be evaluated")) 0 "if.6") 
  (test-expression '(if #f (error "should not be evaluated") 1) 1 "if.7") 

  ; not
  (display "testing not expressions...\n")
  (test-expression '(not #t) #f "not.1")
  (test-expression '(not #f) #t "not.2")


  ; lambda 
  (display "testing lambda expressions...\n")
  (test-expression '((lambda () (+ 3 5))) 8 "lambda.1")
  (test-expression '((lambda (x) (* 3 x)) 5) 15 "lambda.2")
  (test-expression '((lambda (x y) (+ x y)) 3 4) 7 "lambda.3")
  (test-expression '((lambda () 45)) 45 "lambda.4")
  (test-expression '((lambda (x) (+ x 7)) 5) 12 "lambda.5")
  (test-expression '(let ((x 5)) ((lambda (u v) (+ u v)) x 6)) 11 "lambda.6")
;  (test-expression '((lambda arg (apply + arg)) 1 2 3 4 5) 15 "lambda.7")

  (test-expression 
    '((lambda (x y z . t) (+ x y z (apply + t))) 1 2 3) 6 "lambda.8")
;  (test-expression 
;    '((lambda (x y z . t) (+ x y z (apply + t))) 1 2 3 4) 10 "lambda.9")
;  (test-expression 
;    '((lambda (x y z . t) (+ x y z (apply + t))) 1 2 3 4 5) 15 "lambda.10")

;  (let ((env ((global-env 'extended) '(y) '(5))))
;    (test-expression '((lambda (x) (+ x y)) 6) 11 "lambda.11" env))

  ; begin
  (display "testing begin expressions...\n")
  (test-expression '(begin 1 2 3 4) 4 "begin.1")

  ; cond
  (display "testing cond expressions...\n")
  (test-expression '(cond (#t 0) (#f 1) (#f 2) (else 3)) 0 "cond.1")
  (test-expression '(cond (#t 0) (#t 1) (#f 2) (else 3)) 0 "cond.2")
  (test-expression '(cond (#t 0) (#f 1) (#t 2) (else 3)) 0 "cond.3")
  (test-expression '(cond (#t 0) (#t 1) (#t 2) (else 3)) 0 "cond.4")
  (test-expression '(cond (#f 0) (#t 1) (#f 2) (else 3)) 1 "cond.5")
  (test-expression '(cond (#f 0) (#t 1) (#t 2) (else 3)) 1 "cond.6")
  (test-expression '(cond (#f 0) (#f 1) (#t 2) (else 3)) 2 "cond.7")
  (test-expression '(cond (#f 0) (#f 1) (#f 2) (else 3)) 3 "cond.8")
  (test-expression '(cond (#f 0) (else 4)) 4 "cond.9")
  (test-expression '(cond (else 5)) 5 "cond.10")
  
  ; or
  (display "testing or expressions...\n")
  (test-expression '(or #t nonsense1 nonsense2) #t "or.1")
  (test-expression '(or #f #t nonsense) #t "or.2")
  (test-expression '(or #f #f #t) #t "or.3")
  (test-expression '(or #f #f #f) #f "or.4")
  (test-expression '(or) #f "or.5")
  (test-expression '(or #t) #t "or.6")
  (test-expression '(or #f) #f "or.7")

  ; and
  (display "testing and expressions...\n")
  (test-expression '(and #f nonsense1 nonsense2) #f "and.1")
  (test-expression '(and #t #f nonsense) #f "and.2")
  (test-expression '(and #t #t #f) #f "and.3")
  (test-expression '(and #t #t #t) #t "and.4")
  (test-expression '(and) #t "and.5")
  (test-expression '(and #f) #f "and.6")
  (test-expression '(and #t) #t "and.7")

  ; let
  (display "testing let expressions...\n")
  (test-expression '(let ((x 5)) (+ x 7)) 12 "let.1")
  (test-expression '(let ((x 5) (y 3)) (+ x y)) 8 "let.2")
  (test-expression '(let ((x 5) (y 6)) (let ((z 7)) (+ x y z))) 18 "let.3")
  (test-expression '(let ((x 5) (y 6)) (let ((z 7) (x 10)) (+ x y z))) 23 "let.4")
  (test-expression '(let ((x 1)) (let ((y 2)) (let ((z 3)) (+ x y z)))) 6 "let.5")

  ; named-let
  (display "testing named let expressions...\n")
  (test-expression
    '(let loop ((i 5) (acc 1))
       (if (equal? 1 i) acc (loop (- i 1) (* i acc)))) 120 "named-let.1")

  ; let*
  (display "testing let* expressions...\n")
  (test-expression '(let* ((x 5) (y (+ x 2))) (+ x y)) 12 "let*.1")


  ; letrec
  (display "testing recursive let expressions...\n")
  (test-expression
    '(letrec
       ((loop (lambda (n) (if (= 0 n) 1 (* n (loop (- n 1)))))))
       (loop 5)) 120 "letrec.1")
 
  ; application
  (display "testing application expressions...\n")
  (test-expression '(+) 0 "application.1")
  (test-expression '(+ 2) 2 "application.2")
  (test-expression '(+ 2 4) 6 "application.3")
  (test-expression '(car '(1 2)) 1 "application.4")
  (test-expression '(cdr '(1 2)) (list 2) "application.5")
  (test-expression '(cons 2 '()) (list 2) "application.6")
  (test-expression '(cons 5 (cons 2 '())) (list 5 2) "application.7")
  (test-expression '(eval (+ 1 2)) 3 "application.8")
  (test-expression '(apply + '(1 2)) 3 "application.9")


  ; defined?
  (display "testing defined? expressions...\n")
  (test-expression '(defined? +) #t "defined?.1")
  (test-expression '(defined? car) #t "defined?.2")
  (test-expression '(defined? cdr) #t "defined?.3")
  (test-expression '(defined? some-random-name) #f "defined?.4")
  (test-expression '(defined? (this is not even a name)) #f "defined?.5")

  ; thunk
  (display "testing thunk ...\n")
  (let ((thunk (make-thunk '(+ 1 1) global-env)))
    (assert-equals (thunk? thunk) #t "thunk.1")
    (assert-equals (thunk-expression thunk) '(+ 1 1) "thunk.2")
    (assert-equals (thunk-environment thunk) global-env "thunk.3")
    (assert-equals (thunk-evaluated? thunk) #f "thunk.4")
    (assert-equals (force-thunk thunk) 2 "thunk.5")
    (assert-equals (force-thunk thunk) 2 "thunk.7")
    (assert-equals (force-thunk thunk) 2 "thunk.8")
    (assert-equals (force-thunk thunk) 2 "thunk.9")
    (assert-equals (thunk? thunk) #t "thunk.11")
    (assert-equals (thunk? 0) #f "thunk.12")
    (assert-equals (thunk? #\a) #f "thunk.13")
    (assert-equals (thunk? "a") #f "thunk.14")
    (assert-equals (thunk? #t) #f "thunk.15")
    (assert-equals (thunk? #f) #f "thunk.16"))

  ; load
  (display "testing loading files ...\n") 
;  (test-all-files)

  ; higher level interpreters
  (display "testing higher order interpreter ...\n")

  (display "testing native scheme (level 0) ...\n")
  (assert-equals 
    (+ 1 1) 
    2 "higher.0") 

  (display "testing interpreter (level 1) ...\n")
  (assert-equals 
    (strict-eval '(+ 1 1)) 
    2 "higher.1")
  (assert-equals 
    (analyze-eval '(+ 1 1)) 
    2 "higher.2")
  (assert-equals 
    (force-thunk (lazy-eval '(+ 1 1)))
    2 "higher.3")

  (display "setting up higher order interpreter (level 2) ...\n")
  (strict-eval '(load "main.scm"))
  (display "testing higher order interpreter (level 2) ...\n")
  (assert-equals 
    (strict-eval '(strict-eval '(+ 1 1))) 
    2 "higher.4")
  (assert-equals 
    (analyze-eval '(analyze-eval '(+ 1 1))) 
    2 "higher.5")
  (assert-equals 
    (force-thunk (lazy-eval '(force-thunk (lazy-eval '(+ 1 1))))) 
    2 "higher.6")

  (display "unit-test: test complete\n"))

(unit-test)
(exit 0)
