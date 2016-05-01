; added for analyze
(define (analyze-variable exp) (lambda (env) ((env 'lookup) exp)))
