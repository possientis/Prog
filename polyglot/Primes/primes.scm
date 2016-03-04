#!/usr/bin/scm
(load "stream.scm")
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
