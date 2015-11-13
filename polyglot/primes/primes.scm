; this implementation of stream is probably highly inefficient
; and/or bugged, to the point that the following code does not
; work beyond a very low number of requested primes (1000 fails)
(load "stream.scm")
(define (sieve s)
  (stream-cons (s 'car)
               (sieve (stream-filter
                        (lambda (x)
                          (not (= 0 (modulo x (s 'car)))))
                        (s 'cdr)))))

(define primes (sieve (integers-from 2))) 
(display (stream-take 1000 primes))(newline)

(exit 0)

