(define s
  (letrec ((next
             (lambda (n)
               (cons n (delay (next (+ n 1)))))))
    (next 0)))

(define head car)
(define (tail s)
  (force (cdr s)))


(define count 0)
(define p
  (delay
    (begin
      (set! count (+ count 1))
      (if (> count x)
        count
        (force p)))))

(define x 5)
