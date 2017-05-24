; scm only
(require 'macro)
; remove the comma ',' operator below to understand its significance
; remove the '@' below and see what happens



(defmacro (let1 ((name value)) . body)
  `((lambda (,name) ,@body) ,value))

(display (macroexpand '(let1 ((x 5)) (* x x))))(newline)
(display (let1 ((x 5)) (* x x)))(newline)

(define-syntax let2
  (syntax-rules ()
    ((let2 ((name value)) . body)
     ((lambda (name) . body) value))))

(display (macroexpand '(let2 ((x 5)) (* x x))))(newline)  ; doesn't expand
(display (let2 ((x 5)) (* x x)))(newline)


(define-syntax let3 ; quote trick to see expansion
  (syntax-rules ()
    ((let2 ((name value)) . body)
     '((lambda (name) . body) value))))     ; see the quote


(display (let3 ((x 5)) (* x x)))(newline)   ; ((lambda (x) (* x x)) 5)



(exit 0)



