(define stream1
  ; public interface
  (let ((this (lambda (data)  ;; (define (this data) ... but no name leakage
    (lambda (m)
      (cond ((eq? m 'car) (car data))
            ((eq? m 'cdr) (force (cdr data)))
            ((eq? m 'null?) (eq? #f data))
            (else (display "stream: unknown operation error\n")))))))
    (lambda args
      (if (null? args)
        (this #f)
        (this (cons (car args) (cadr args)))))))


