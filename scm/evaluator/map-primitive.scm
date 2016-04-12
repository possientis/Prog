(define (map-primitive procedure seq) ; quick and dirty, one dimension
  (cond ((null? seq) '())
        (else (cons (apply procedure (list (car seq))) 
                    (map-primitive procedure (cdr seq))))))



;(display (map + '(1 2 3) '(4 5 6)))(newline)
