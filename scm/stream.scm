; overriding built-ins. This may be unnecessary
(define (delay x)
  (lambda() (eval x)))

(define (force a)
  (a))


; stream class
(define stream  ; stream constructor
  ;
  ; static private member
  (let ((stream-cons
          (lambda (x y)
            'ok   ; to be implemented
            ))
        (stream-new
          (lambda()
            (stream '())))) ; returns an empty stream

  ;
  (lambda args  ; (possibly empty) list of constructor arguments
    ;
    ; public interface
    (define (this m)
      (cond ((eq? m 'car) (stream-car))
            ((eq? m 'cdr) (stream-cdr))
            ((eq? m 'cons) stream-cons)
            ((eq? m 'null?) (stream-null?))
            ((eq? m 'new)(stream-new))
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


(define (stream-ref s n)
  (if (= n 0)
    (s 'car)
    (stream-ref (s 'cdr) (- n 1))))

(define (stream-map proc s)
  (if (s 'null?)
    ((stream) 'new)
    (((stream) 'cons) (proc (s 'car)) (stream-map proc (s 'cdr)))))

(define (stream-for-each proc s)
  (if (s 'null?)
    'done
    (begin
      (proc (s 'car))
      (stream-for-each proc (s 'cdr)))))

(define (stream-display s)
  (define (view x)
    (display x)(newline))
  (stream-for-each view s))

(define s (stream))
(define f (lambda (x) (* x x)))
(define g (lambda (x) (display "g is running\n")))
(define t (stream-map f s))
(stream-for-each g s)
(stream-display s)




