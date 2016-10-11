; need list of primes 'primes' to be defined
(define (prime? n)
  (if (< n 2) #f
    ; else
    (let loop ((s primes))
      (let ((p (s 'car)))
        (cond ((> (* p p) n) #t)
              ((= 0 (modulo n p)) #f)
              (else (loop (s 'cdr))))))))


