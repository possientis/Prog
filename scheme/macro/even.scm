; (require 'macro) ; doesnt work with scm anyway
; guile only

(define x
  (let ()
    (define even? 
              (lambda (x)
                (or (= x 0) (odd? (- x 1)))))
    (define-syntax odd?
      (syntax-rules ()
        ((_ x) (not (even? x)))))
    (even? 10)))

(display "x = ")(display x)(newline)

