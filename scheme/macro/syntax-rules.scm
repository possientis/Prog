;(require 'macro) ; uncomment for scm

;(syntax-rules literals (pattern template) ...

; patterns (see macro.scm for examples)
; (when condition exp ...)
; (unless condition exp ..)
; (my-or)
; (my-or exp)
; (my-or exp rest ...)

(define-syntax kwote
  (syntax-rules ()  ; no literals
    ((kwote exp)
     (quote exp))))

(display (kwote (foo . bar))) ; (foo . bar)

(define-syntax let1
  (syntax-rules ()
    ((let1 ((var vals) ...) . exp)       ; using improper list '.', not that good
     (let ((var vals) ...) . exp))))     ; as will match non lists

(newline)
(display (let1 ((x 5)(y 3)) (+ x y)))  ; 8

  
(define-syntax let2
  (syntax-rules ()
    ((let2 ((var vals) ...) exp ...)    ; body has zero or more expressions   
     (let ((var vals) ...) exp ...))))  

(newline)
(display (let2 ((x 5)(y 3)) (+ x y)))  ; 8

(define-syntax let3
  (syntax-rules ()
    ((let3 ((var vals) ...) exp exp* ...)    ; body has one or more expressions   
     (let ((var vals) ...) exp exp* ...))))  

(newline)
(display (let3 ((x 5)(y 3)) (+ x y)))  ; 8


(define-syntax letv
  (syntax-rules ()
    ((letv #((var val) ...) exp exp* ...)    ; vector pattern
     (let ((var val) ...) exp exp* ...))))

(newline)
(display (letv #((x 5)(y 3)) (+ x y)))  ; 8

(define-syntax cond1
  (syntax-rules (=> else)
    ((cond1 test => fun)
     (let ((exp test))
       (if exp (fun exp) #f)))
    ((cond1 test exp exp* ...)
     (if test (begin exp exp* ...)))
    ((cond1 else exp exp* ...)
     (begin exp exp* ...))))

(newline)
(define (square x) (* x x))
(display (cond1 10 => square))          ; 100

(newline)
(let ((=> #t))  ; identifier '=> is now bound, will not macth literal
  (display (cond1 10 => square)))       ; #<procedure square (x)>


(define-syntax define-matcher-macro
  (syntax-rules ()
    ((_ name lit)
     (define-syntax name
       (syntax-rules ()
         ((_ lit) #t)
         ((_ else) #f))))))

(define-matcher-macro is-literal-foo? "foo")  ; defines new macro for is-literal-foo?

(newline)
(display (is-literal-foo? "foo"))      ; #t 
(newline)
(display (is-literal-foo? "bar"))      ; #f

(newline) ; mtachingoccurs at expansion-time, not run-time
(display (let ((foo "foo")) (is-literal-foo? foo))) ; #f


(exit 0)
