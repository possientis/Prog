(define (flatten l)
  (if (not (list? l))
    (display "flatten: argument is not a list error\n")
    (cond ((null? l) '())
          ((list? (car l))
           (append (flatten (car l)) (flatten (cdr l))))
          (else (cons (car l) (flatten (cdr l)))))))

(define (sorted? l)
  (cond ((null? l) #t)
        ((null? (cdr l)) #t)
        (else
          (and (<= (car l) (cadr l))
               (sorted? (cdr l))))))




