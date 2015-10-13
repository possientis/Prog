(define stream  ; stream constructor
  ;
  ; static private member
  (let ((stream-cons
          (lambda (x y)
            'ok   ; to be implemented
            )))
  ;
  (lambda args  ; (possibly empty) list of constructor arguments
    ;
    ; public interface
    (define (this m)
      (cond ((eq? m 'car) (stream-car))
            ((eq? m 'cdr) (stream-cdr))
            ((eq? m 'cons) stream-cons)
            ((eq? m 'null?) (stream-null?))
            (else (display "stream: unknown operation error\n"))))
    (define (stream-car)
      #f)
    (define (stream-cdr)
      this)
    (define (stream-null?)
      #t)
    ;
    ;returning public interface
    this)))


(define s (stream))

(define (stream-ref s n)
  (if (= n 0)
    (s 'car)
    (stream-ref (s 'cdr) (- n 1))))
