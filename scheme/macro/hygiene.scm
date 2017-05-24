(define-syntax my-or
  (syntax-rules ()
    ((my-or) #t)
    ((my-or exp) exp)
    ((my-or exp rest ...)
     (let ((t exp))
       (if t t (my-or rest ...))))))

(newline)
(display (let ((t #t)) (my-or #f t))) ; #t , phew !!!

; a naive expansion would yield:
; (my-or #f t) -> (let ((t #f))
;                   (if t t (my-or t)))

