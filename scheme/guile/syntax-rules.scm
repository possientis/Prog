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





(exit 0)
