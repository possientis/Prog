(define this    
  (lambda args
  (lambda (m)
    (cond ((eq? m 'car) 'myImpl)
          ((eq? m 'cdr) (data 'cdr))
          ((eq? m 'cons)(data 'cons))
          ((eq? m 'null?)(data 'null?))
          (else (display "Unkown operation error\n"))))))

(define Impl
  (begin
    (define (stream-car s) (car s))
    (define (stream-cdr s) (cdr s))
    (define (stream-null? s) (null? s))
    (define (stream-cons s) (lambda (x) (cons x s))i)))






