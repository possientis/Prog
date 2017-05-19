;(require 'macro)

(define-syntax or
  (lambda (x)
    (syntax-case x ()
      ((or)   (syntax #f)
      ((or e) (syntax e)))



(exit 0)
