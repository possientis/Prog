(load "main.scm")

(define (assert-equals left right message)
  (if (not (equal? left right)) 
    (error "unit-test failure: "
           (string-append message 
                          ": value = " (object->string left)
                          ": expected = " (object->string right)))))

(define (test-expression exp value message . arg)
  (let ((env (if (null? arg) global-env (car arg))) 
        (print (lambda (msg) (string-append message msg)))
        (mode (get-eval-mode))) ; save eval mode to be restored
    ; strict-eval (testing in all three modes)
    (set-eval-mode 'strict)
    (assert-equals (strict-eval exp env) value (print ": strict-eval (strict)")) 
    (set-eval-mode 'lazy)
    (assert-equals (strict-eval exp env) value (print ": strict-eval (lazy)")) 
    (set-eval-mode 'analyze)
    (assert-equals (strict-eval exp env) value (print ": strict-eval (analyze)")) 
    (set-eval-mode mode)
    ; lazy-eval (testing in all three modes)
    (set-eval-mode 'strict)
    (assert-equals (force-thunk (lazy-eval exp env)) value (print ": lazy-eval")) 
    (set-eval-mode 'lazy)
    (assert-equals (force-thunk (lazy-eval exp env)) value (print ": lazy-eval")) 
    (set-eval-mode 'analyze)
    (assert-equals (force-thunk (lazy-eval exp env)) value (print ": lazy-eval")) 
    (set-eval-mode mode)
    ; analyze (testing in all three modes)
    (set-eval-mode 'strict)
    (assert-equals ((analyze exp) env) value (print ": analyze"))
    (set-eval-mode 'lazy)
    (assert-equals ((analyze exp) env) value (print ": analyze"))
    (set-eval-mode 'analyze)
    (assert-equals ((analyze exp) env) value (print ": analyze"))
    (set-eval-mode mode)
    ; new-eval (strict)
    (set-eval-mode 'strict)
    (assert-equals (new-eval exp env) value (print ": new-eval (strict)"))
    ; new-eval (lazy)
    (set-eval-mode 'lazy)
    (assert-equals (force-thunk(new-eval exp env))value(print ": new-eval (lazy)"))
    ; new-eval (analyze)
    (set-eval-mode 'analyze)
    (assert-equals (new-eval exp env) value (print ": new-eval (analyze)"))
    (set-eval-mode mode)))  ; restoring eval mode

(define (test-thunk exp value message . arg)
  (let ((env (if (null? arg) global-env (car arg))) 
        (print (lambda (msg) (string-append message msg)))
        (mode (get-eval-mode))) ; save eval mode to be restored
    (assert-equals 
      (force-thunk (strict-eval exp env)) value (print ": strict-eval")) 
    (assert-equals 
      (force-thunk (lazy-eval exp env)) value (print ": lazy-eval")) 
    (assert-equals 
      (force-thunk ((analyze exp) env)) value (print ": analyze"))
    (set-eval-mode 'strict)
    (assert-equals 
      (force-thunk (new-eval exp env)) value (print ": new-eval (strict)"))
    (set-eval-mode 'lazy)
    (assert-equals 
      (force-thunk(new-eval exp env))value(print ": new-eval (lazy)"))
    (set-eval-mode 'analyze)
    (assert-equals 
      (force-thunk (new-eval exp env)) value (print ": new-eval (analyze)"))
    (set-eval-mode mode)))  ; restoring eval mode


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
  (let ((car-primitive (make-primitive-procedure car)))
    (test-expression car-primitive car-primitive  "self-evaluating.8"))
  (let ((eval-square (make-eval-procedure '(x) '(* x x) global-env)))
    (test-expression eval-square eval-square "self-evaluating.9"))
  (let ((analyze-square (make-analyze-procedure '(x) '(* x x) global-env)))
    (test-expression analyze-square analyze-square "self-evaluating.10"))
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
  (test-expression 'apply (make-primitive-procedure new-apply) "variable.11")
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
  (test-expression 'close-port (make-primitive-procedure close-port) "variable.25")
  (test-expression 'cons (make-primitive-procedure cons) "variable.26")
  (test-expression 'display (make-primitive-procedure new-display) "variable.27")
  (test-expression 'eof-object?(make-primitive-procedure eof-object?)"variable.28")
  (test-expression 'eq? (make-primitive-procedure eq?) "variable.29")
  (test-expression 'equal? (make-primitive-procedure equal?) "variable.30")
  (test-expression 'error (make-primitive-procedure error) "variable.31")
  (test-expression 'eval (make-primitive-procedure new-eval) "variable.32")
  (test-expression 'exit (make-primitive-procedure exit) "variable.33")
  (test-expression 'hash (make-primitive-procedure hash) "variable.34")

  (test-expression 
    'inexact->exact (make-primitive-procedure inexact->exact) "variable.35")

  (test-expression 'length (make-primitive-procedure length) "variable.36")
  (test-expression 'list (make-primitive-procedure list) "variable.37")
  (test-expression 'load (make-primitive-procedure new-load) "variable.38")
  (test-expression 'make-vector(make-primitive-procedure make-vector)"variable.39")
  (test-expression 'map (make-primitive-procedure new-map) "variable.40")
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

  (test-expression 'vector-ref (make-primitive-procedure vector-ref) "variable.59")
  (test-expression 'vector-set!(make-primitive-procedure vector-set!)"variable.60")
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
  ; assigment
  (display "testing assignment expressions...\n")
  ;
  (let ((env ((global-env 'extended) 'var #f))    ; extended env with var = #f
        (mode (get-eval-mode)))                   ; so we can restore it later
    (test-expression 'var #f "assignment.1" env)    
    ; strict assignment
    (let ((result (strict-eval '(set! var #t) env)))
      (assert-equals result unspecified-value "assignment.2")
      (test-expression 'var #t "assignment.3" env))     ; testing outcome 
    ; lazy assignment : cannot use test-expression in this case, because
    ; of weird semantics of lazy assignment followed by strict-eval which
    ; returns a thunk, despite being strict. Not sure how to fix this
    (let ((result (lazy-eval '(set! var #\a) env))
          (mode (get-eval-mode))) 
      (assert-equals (force-thunk result) unspecified-value "assignment.4")
      (assert-equals (force-thunk (strict-eval 'var env)) #\a "assignment.5")
      (assert-equals (force-thunk (lazy-eval 'var env)) #\a "assignment.6")
      (assert-equals (force-thunk ((analyze 'var) env)) #\a "assignment.7")
      (set-eval-mode 'strict)
      (assert-equals (force-thunk (new-eval 'var env)) #\a "assignment.6")
      (set-eval-mode 'lazy)
      (assert-equals (force-thunk (new-eval 'var env)) #\a "assignment.7")
      (set-eval-mode 'analyze)
      (assert-equals (force-thunk (new-eval 'var env)) #\a "assignment.8")
      (set-eval-mode mode))  ; restoring eval mode
    ; analyzed assignment
    (let ((result ((analyze '(set! var 45)) env)))
      (assert-equals result unspecified-value "assignment.9")
      (test-expression 'var 45 "assignment.10" env))     ; testing outcome
    ; strict assignment via new-eval
    (set-eval-mode 'strict)
    (let ((result (new-eval '(set! var "abc") env)))
      (assert-equals result unspecified-value "assignment.11")
      (test-expression 'var "abc" "assignment.12" env))  ; testing outcome
    ; lazy assignment via new-eval (cannot use test-expression)
    (set-eval-mode 'lazy)
    (let ((result (new-eval '(set! var 4.5) env))
          (mode (get-eval-mode)))
      (assert-equals (force-thunk result) unspecified-value "assignment.13")
      (assert-equals (force-thunk (strict-eval 'var env)) 4.5 "assignment.14")
      (assert-equals (force-thunk (lazy-eval 'var env)) 4.5 "assignment.15")
      (assert-equals (force-thunk ((analyze 'var) env)) 4.5 "assignment.16")
      (set-eval-mode 'strict)
      (assert-equals (force-thunk (new-eval 'var env)) 4.5 "assignment.17")
      (set-eval-mode 'lazy)
      (assert-equals (force-thunk (new-eval 'var env)) 4.5 "assignment.18")
      (set-eval-mode 'analyze)
      (assert-equals (force-thunk (new-eval 'var env)) 4.5 "assignment.19")
      (set-eval-mode mode))  ; restoring eval mode
    ; analyzed assignment via new-eval 
    (set-eval-mode 'analyze)
    (let ((result (new-eval '(set! var '()) env)))
      (assert-equals result unspecified-value "assignment.20")
      (test-expression 'var '() "assignment.21" env))    ; testing outcome
    ; retoring eval mode
    (set-eval-mode mode))

    
  ; definition
  (display "testing definition expressions...\n")

  (let ((env ((global-env 'extended) 'var #f))    ; some extension of global env
        (mode (get-eval-mode)))                   ; so we can restore it later
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
    ; lazy definition (cannot use 'test-expression', need 'test-thunk')
    (let ((result (lazy-eval '(define var 0.3) env))
          (mode (get-eval-mode)))
      (assert-equals (force-thunk result) unspecified-value "definiton.12")
      (assert-equals ((env 'defined?) 'var) #t "definition.13")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.14")
      (test-thunk 'var 0.3 "definition.15" env)
      ((env 'delete!) 'var)
      (assert-equals ((env 'defined?) 'var) #f "definition.21")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.22"))
    ; analyze definition
    (let ((result ((analyze '(define var "hello")) env)))
      (assert-equals result unspecified-value "definiton.23")
      (assert-equals ((env 'defined?) 'var) #t "definition.24")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.25")
      (test-expression 'var "hello" "definition.26" env)
      ((env 'delete!) 'var)
      (assert-equals ((env 'defined?) 'var) #f "definition.27")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.28"))
    ; strict definition via new-eval
    (set-eval-mode 'strict)
    (let ((result (new-eval '(define var #\a) env)))
      (assert-equals result unspecified-value "definiton.29")
      (assert-equals ((env 'defined?) 'var) #t "definition.30")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.31")
      (test-expression 'var #\a "definition.32" env)
      ((env 'delete!) 'var)
      (assert-equals ((env 'defined?) 'var) #f "definition.33")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.34"))
    ; lazy definition via new-eval (need to use 'test-thunk)
    (set-eval-mode 'lazy)
    (let ((result (new-eval '(define var #t) env))
          (mode (get-eval-mode)))
      (assert-equals (force-thunk result) unspecified-value "definiton.35")
      (assert-equals ((env 'defined?) 'var) #t "definition.36")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.37")
      (test-thunk 'var #t "definition.38" env)
      ((env 'delete!) 'var)
      (assert-equals ((env 'defined?) 'var) #f "definition.44")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.45"))
    ; analyze definition via new-eval
    (set-eval-mode 'analyze)
    (let ((result ((analyze '(define var #f)) env)))
      (assert-equals result unspecified-value "definiton.46")
      (assert-equals ((env 'defined?) 'var) #t "definition.47")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.48")
      (test-expression 'var #f "definition.49" env)
      ((env 'delete!) 'var)
      (assert-equals ((env 'defined?) 'var) #f "definition.50")
      (assert-equals ((global-env 'defined?) 'var) #f "definition.51"))
    (set-eval-mode mode)
    ; strict definition: function with no argument
    (let ((result (strict-eval '(define (f) 12) env)))
      (assert-equals result unspecified-value "definiton.52")
      (assert-equals ((env 'defined?) 'f) #t "definition.53")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.54")
      (test-expression '(f) 12 "definition.55" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.56")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.57"))
    ; lazy definition: function with no argument (can use 'test-expression')
    (let ((result (lazy-eval '(define (f) 0.3) env))
          (mode (get-eval-mode)))
      (assert-equals (force-thunk result) unspecified-value "definiton.58")
      (assert-equals ((env 'defined?) 'f) #t "definition.59")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.60")
      (test-expression '(f) 0.3 "definition 61" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.62")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.63"))
    ; analyze definition: function with no argument
    (let ((result ((analyze '(define (f) "hello")) env)))
      (assert-equals result unspecified-value "definiton.64")
      (assert-equals ((env 'defined?) 'f) #t "definition.65")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.66")
      (test-expression '(f) "hello" "definition.67" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.68")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.69"))
    ; strict definition via new-eval: function with no argument
    (set-eval-mode 'strict)
    (let ((result (new-eval '(define (f) #\a) env)))
      (assert-equals result unspecified-value "definiton.70")
      (assert-equals ((env 'defined?) 'f) #t "definition.71")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.72")
      (test-expression '(f) #\a "definition.73" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.74")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.75"))
    ; lazy definition via new-eval: function with no argument
    (set-eval-mode 'lazy)
    (let ((result (new-eval '(define (f) #t) env)))
      (assert-equals (force-thunk result) unspecified-value "definiton.76")
      (assert-equals ((env 'defined?) 'f) #t "definition.77")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.78")
      (test-expression '(f) #t "definition.79" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.79")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.80"))
    ; analyze definition via new-eval: function with no argument
    (set-eval-mode 'analyze)
    (let ((result (new-eval '(define (f) #f) env)))
      (assert-equals result unspecified-value "definiton.81")
      (assert-equals ((env 'defined?) 'f) #t "definition.82")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.83")
      (test-expression '(f) #f "definition.84" env)
      ((env 'delete!) 'f)
      (assert-equals ((env 'defined?) 'f) #f "definition.85")
      (assert-equals ((global-env 'defined?) 'f) #f "definition.86"))
    (set-eval-mode mode)

    )
 

  ; syntactic sugar for named functions
  (let ((x (new-eval '(define (f x) (* x x)))))
    (if (not (equal? (new-eval '(f 5)) 25))
      (display "unit-test: test 5.7 failing\n"))
    ((global-env 'delete!) 'f))
  (let ((x (new-eval '(define (f x y) (+ x y)))))
    (if (not (equal? (new-eval '(f 3 4)) 7))
      (display "unit-test: test 5.8 failing\n"))
    ((global-env 'delete!) 'f))
 
 ; syntactic sugar for named functions
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

  (let ((thunk (make-thunk '(+ 1 1) global-env)))
    (assert-equals (thunk? thunk) #t "thunk.1")
    (assert-equals (thunk-expression thunk) '(+ 1 1) "thunk.2")
    (assert-equals (thunk-environment thunk) global-env "thunk.3")
    (assert-equals (thunk-evaluated? thunk) #f "thunk.4")
    (assert-equals (force-thunk thunk) 2 "thunk.5")
    (assert-equals (thunk-evaluated? thunk) #t "thunk.6")
    (assert-equals (force-thunk thunk) 2 "thunk.7")
    (assert-equals (force-thunk thunk) 2 "thunk.8")
    (assert-equals (force-thunk thunk) 2 "thunk.9")
    (assert-equals (thunk-evaluated? thunk) #t "thunk.10")
    (assert-equals (thunk? thunk) #t "thunk.11")
    (assert-equals (thunk? 0) #f "thunk.12")
    (assert-equals (thunk? #\a) #f "thunk.13")
    (assert-equals (thunk? "a") #f "thunk.14")
    (assert-equals (thunk? #t) #f "thunk.15")
    (assert-equals (thunk? #f) #f "thunk.16")
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
