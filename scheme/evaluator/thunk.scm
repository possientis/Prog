;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-thunk)) 
  (begin
    (define included-thunk #f) (display "loading thunk")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; When attempting to determine whether an object is a thunk using the 'thunk?'
; function, the interpreter simply checks for a tag 'thunk. This creates a bug,
; as it is possible for a data stucture to appear as a thunk without being one:
; For example, imagine our interpreter (implemented in native scheme) is running 
; its own code: we obtain a second level interpreter which is running in inter-
; preted code rather than native scheme. This second level interpreter will handle
; data structures with a 'thunk tag and which it considers to be a thunk object.
; However, from the point of view of the first level interpreter running in native
; scheme, such data structure is not a thunk, and wrongly viewing it as a thunk
; generates an error. Suppose we run the following code in native scheme:
;
; (load "main.scm")                 ; define 'strict-eval and dependencies
; (strict-eval '(load "main.scm"))
; 
; When running (load "main.scm") in native scheme, we are defining the function
; 'strict-eval', which allows us to run our interpreter.
;
; (display (strict-eval '(+ 1 1)))  ; 2
;
; By running (strict-eval '(load "main.scm")) in native scheme, we are asking
; our interpreter to run (load "main.scm"), hence creating all necessary bindings
; in the interpreter's global environment to use 'strict-eval in interpreted code:
;
; (display (strict-eval '(strict-eval '(+ 1 1)))) ; 2
;
; We can also create a thunk object in interpreted code:
;
; (strict-eval '(define t (make-thunk '(+ 1 1) global-env)))
;
; The intepreter's global environment now has a binding for the variable t
;
; (define value ((global-env 'lookup) 't))
;
; And we can inspect the value associated with this variable:
;
; (display value)
;
; (thunk (eval-procedure (m) (begin (cond ((eq? m (quote value)) (value data)) 
; ((eq? m (quote expression)) (expression data)) ((eq? m (quote environment)) 
; (environment data)) ((eq? m (quote evaluated?)) (evaluated? data)) (else 
; (error thunk: unknown operation error m)))) 
; #<CLOSURE <anon> "environment1.scm": (m)>))
; 
; This native scheme value is of the form (thunk object) and deceptively appears
; to be a thunk. However, in order for this value to qualify as a thunk, 'object'
; would need to be a native scheme object which it is not. 'object' is in fact
; a data sructure used by our interpreter to represent a procedure. In short,
; 'object' is an interpreted scheme object, not a native scheme object. 
; If our native scheme interpreter wrongly interprets this 'value' as a thunk,
; it will wrongly regard 'object' as a native scheme procedure and attempt to
; run it when forcing the thunk, thereby creating an error.
;
; Hence, when implementing the function thunk? which determines whether an
; object is of type thunk, we need to be able to distinguish the true thunks
; of our native scheme interpreter, from the data structures which are thunks
; of a higher level interpreter. We do this by using a different tag 'thunk0'
; 'thunk1', 'thunk2', etc... depending on the level of the intepreter which is 
; running. One way to make the code self-aware of its running level is to 
; evaluate the operator +. In native scheme, this operator evaluates to:
;
; (display +)                 ; #<primitive-procedure +>
; 
; while our interpreter evaluates + as:
; 
; (display (strict-eval '+))  ;(primitive-procedure #<primitive-procedure +>)
;
; and (display (strict-eval '(strict-eval '+))) returns the list:
;
; (primitive-procedure (primitive-procedure #<primitive-procedure +>))
;
; Hence we can implement a function scheme-interpreter-level as follows:

(define (scheme-interpreter-level)
  (let loop ((test +))
    (if (not (list? test))
      0                             ; test is #<primitive-procedure>
      (+ 1 (loop (cadr test))))))   ; test is (primitive-procedure ... )

; We can now implement a thunk-tag function which generates a different tag
; for each scheme interpreter level, simply by appending a number to "thunk".
; For performance reason, this function is memoized:

(define (thunk-tag)
  (let ((tag #f))   ; memoization
    (if (eq? #f tag)
      (set! tag (string->symbol 
                  (string-append 
                    "thunk" 
                    (number->string (scheme-interpreter-level))))))
    tag))


; testing
(define (thunk? obj) 
  (tagged-list? obj (thunk-tag)))

; making
(define make-thunk   ; constructor
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'value) (value data))
              ((eq? m 'expression) (expression data))
              ((eq? m 'environment) (environment data))
              ((eq? m 'evaluated?) (evaluated? data))
              (else (error "thunk: unknown operation error" m)))))
    ;
    (define (expression data) (cadr data))
    ;
    (define (environment data) (caddr data))
    ;
    (define (evaluated? data) (null? (environment data)))
    ;
    ; This function is called when a thunk is forced. An evaluation of the
    ; thunk needs to take place and the question naturally arises of which 
    ; evaluation function to call. We cannot use 'new-eval` as this would
    ; fail to do anything when eval-mode is 'lazy'. Hence we need to use
    ; either 'strict-eval' or 'analyze'.
    (define (value data)
      (let ((expr (expression data))
            (env  (environment data)))
        (if (evaluated? data)
          expr
          (let ((value (strict-eval expr env)))
            (set-car! (cdr data) value) ; replacing expression by its value
            (set-car! (cddr data) '())  ; discarding environment for gb release
            value))))
    ;
    ; returning two argument constructor
    ;
    (lambda (expr env) 
      (if (thunk? expr) ; do not create a double thunk
        expr
        (list (thunk-tag) (this (list 'data expr env)))))))

; destructuring
(define (thunk-expression obj) ((cadr obj) 'expression))
(define (thunk-environment obj) ((cadr obj) 'environment))
(define (thunk-evaluated? obj) ((cadr obj) 'evaluated?))
(define (thunk-value obj) ((cadr obj) 'value))

; Note that we do not throw an error when argument to force-thunk is not a 
; thunk. This has the disadvantage of removing possible detection of logic
; errors. However, considering we are mixing various types of evaluations
; (strict, lazy, analyze), the logic is not very clear anyway, and we often
; end up with unexpected thunks in the evaluation process. This laxed semantics 
; of force-thunk allows us to remove possible thunks in a list of arguments. 
; (See the module primitive-procedure)
; forcing
(define (force-thunk obj)
  (if (thunk? obj) (thunk-value obj) obj))

))  ; include guard

