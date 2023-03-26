(load "stream.scm")
; this code uses the default implementation of 'force' and 'delay'
; in particular, 'delay' has a memoizing scheme embedded.
; Interestingly, memoizing does not improve performance in this case.
; If anything, the code is slightly slower with memoization

; passing command line arguments to scheme scm script
(define arguments (program-arguments))
(define num-primes (string->number (caddr arguments)))
(define (sieve s)
  (stream-cons (s 'car)
               (sieve (stream-filter
                        (lambda (x)
                          (not (= 0 (modulo x (s 'car)))))
                        (s 'cdr)))))

(define primes (sieve (integers-from 2))) 

(display (stream-take num-primes primes))(newline)
(exit 0)
