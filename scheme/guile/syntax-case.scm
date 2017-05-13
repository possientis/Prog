(define-syntax when1
  (syntax-rules ()
    ((when1 test e e* ...)
     (if test (begin e e* ...)))))


(define-syntax when2
  (lambda (x)
    (syntax-case x ()
      ((when2 test e e* ...)
       #'(if test (begin e e* ...))))))

(when1 #t (display "when1: this is true\n"))
(when1 #f (display "when1: this should never appear\n"))
(when2 #t (display "when2: this is true\n"))
(when2 #f (display "when2: this should never appear\n"))

(display (syntax (foo bar baz)))(newline)
; (
;   #(syntax-object foo ((top)) (hygiene guile-user)) 
;   #(syntax-object bar ((top)) (hygiene guile-user)) 
;   #(syntax-object baz ((top)) (hygiene guile-user))
; )

(define-syntax add1
  (lambda (x)
    (syntax-case x ()
      ((add1 expr)
       (syntax (+ expr 1))))))

(display (add1 (+ 2 (* 5 3))))(newline)   ; 18

; #' for syntax objects is similar to ' for quotes
(display (syntax foo))(newline) ; #(syntax-object foo ((top)) (hygiene guile-user))
(display #'foo )(newline)       ; #(syntax-object foo ((top)) (hygiene guile-user))

; syntax-rules define from syntax-case:
(define-syntax syntax-rules
  (lambda (x)
    (syntax-case x ()
      ((_ (k ...) ((keyword . pattern) template) ...)
       #'(lambda (x)
           (syntax-case x (k ...)
             ((dummy . pattern) #'template)
             ...))))))

(display (identifier? #'foo))   (newline)   ; #t
(display (identifier? #'(+1 1)))(newline)   ; #f

(define-syntax add1!
  (lambda (x)
    (syntax-case x ()
      ((_ var) (identifier? #'var)
       #'(set! var (add1 var))))))


(define foo 0)
(add1! foo)
(display foo)(newline)    ; 1
(add1! "not-an-indentifier")










(exit 0)
