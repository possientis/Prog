(load "stream.scm")
(define (sieve s)
  (stream-cons (s 'car)
               (sieve (stream-filter
                        (lambda (x)
                          (not (= 0 (modulo x (s 'car)))))
                        (s 'cdr)))))

(define primes (sieve (integers-from 2))) 

(define (prime? n)
  (if (< n 2) #f
    ; else
    (let loop ((s primes))
      (let ((p (s 'car)))
        (cond ((> (* p p) n) #t)
              ((= 0 (modulo n p)) #f)
              (else (loop (s 'cdr))))))))

(display (stream-take 1000 primes))(newline)
(exit 0)
