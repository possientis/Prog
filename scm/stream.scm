(require 'macro)  ; 'syntax-rules unbound otherise
; see r5rs.pdf page 32
(define-syntax delay
  (syntax-rules
    ()
    ((delay expression)
     (make-promise (lambda () expression)))))
(define-syntax naive-delay
  (syntax-rules
    ()
    ((naive-delay expression)
     (make-naive-promise (lambda() expression)))))

; implementation of force simple
(define (force object)  ; simply calling object
  (object))

; see r5rs.pdf page 33
(define (make-promise proc)
  (let ((ready? #f)(result #f))
    (lambda ()
      (if ready?
        result
        (let ((x (proc)))
          ; here is the key point from r5rs.pdf
          ; "A promise may refer to its own value.
          ; Forcing such a promise may cause the
          ; promise to be forced a second time
          ; before the value of the first force
          ; has been computed."
          ;
          ; Normally, you would expect the code
          ; simply to return 'x at this stage
          ; (after setting ready? and result)
          ; However, the call to proc may be recursive
          ; and may have side effects. So if we
          ; want make sure forcing always returns
          ; the same value, we need to test once
          ; more for ready?
          (if ready?
            result
            (begin
              (set! ready? #t)
              (set! result x)
              result)))))))

; compare with naive promise
(define (make-naive-promise proc)
  (let ((ready? #f)(result #f))
    (lambda()
      (if ready?
        result
        (let ((x (proc)))
          (set! ready? #t)
          (set! result x)
          result)))))



(define ones (cons 1 (delay ones)))

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




