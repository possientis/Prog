; stream.scm
;
; THERE IS A PROBLEM WITH THIS IMPLEMENTATION
; which is probably highly space inefficient (see stream-test and primes)
; possibly leading to stack overflow?
;
; The purpose of this file is to provide an implementation of the stream
; class as described in SICP. We want to be able to define somethings like:
; (define ones (stream-cons 1 ones))
; There is no way this can work if 'stream-cons' is a regular function
; because 'ones' need to be fully evaluated before it is passed to it.
; So stream-cons has to be a special form, not a function.
; Hence we need to introduce a new syntactic feature
(require 'macro)  ; 'syntax-rules unbound otherwise
; and define a new special form 'stream-cons
(define-syntax stream-cons
  (syntax-rules
    ()
    ((stream-cons expr1 expr2)    ; expr2 should return a stream object
     (stream expr1 (delay expr2)))))  ; returning stream object

; bridge
(define (stream . args) 
  (apply stream2 args)) ; can select various implementations here

; more efficient implementation
(define stream2
  (begin
  ; instance members interface
  (define (this data)
    (lambda (m)
      (cond ((eq? m 'car) (car data))
            ((eq? m 'cdr) (force (cdr data)))
            ((eq? m 'null?) (eq? #f data))
            (else (display "stream: unknown operation error\n")))))
  (lambda args
    (if (null? args)
      (this #f)
      (this (cons (car args) (cadr args)))))))

; first implementation
(define (stream1 . args) ; args = '() or args = '(expr1 (delay expr2))
    ;
    ; private data
    (define data #f) ; empty stream, properly initialized below
    ; public interface
    (define (this m)
      (cond ((eq? m 'car) (stream-car))
            ((eq? m 'cdr) (stream-cdr))
            ((eq? m 'null?) (stream-null?))
            (else (display "stream: unknown operation error\n"))))
    ;
    (define (stream-car)
      (car data))               ; no special error handling
    ;
    (define (stream-cdr)
      (force (cdr data)))     ; no special error handling
    ;
    (define (stream-null?)
      (eq? #f data))  ; #f rather than '() for emphasis
    ;
    (define (init)            ; initialization of object
      (if (not (null? args))  ; expecting a pair (value . promise)
        (set! data (cons (car args) (cadr args)))))
    ;
    ; initializing object
    (init)
    ;returning public interface
    this)

; non-member interface of stream
(define (stream-ref s n)
  (if (= n 0)
    (s 'car)
    (stream-ref (s 'cdr) (- n 1))))

(define (stream-filter pred s)
  (if (s 'null?)
    s           ; empty stream
    (if (pred (s 'car))
      (stream-cons (s 'car) (stream-filter pred (s 'cdr)))
      (stream-filter pred (s 'cdr)))))

(define (stream-for-each proc s)
  (if (s 'null?)
    'done
    (begin
      (proc (s 'car))
      (stream-for-each proc (s 'cdr)))))

(define (stream-display s)
  (define (view x)
    (display x)(display " "))
  (display "( ")
  (stream-for-each view s)
  (display ")"))

(define (list->stream seq)
  (if (null? seq)
    (stream)      ; instantiating empty stream
    (stream-cons (car seq) (list->stream (cdr seq)))))

(define (stream-take num myStream)
  (cond ((= 0 num) '())
        ((myStream 'null?) '())
        (else (cons (myStream 'car) (stream-take (- num 1) (myStream 'cdr))))))

(define (integers-from n)
  (stream-cons n (integers-from (+ n 1))))

(define (stream-range lo hi)
  (if (< hi lo) (stream)
    ; else
    (stream-cons lo (stream-range (+ lo 1) hi))))

; proc requires n-arguments. xs is a list of n streams
; no sensible results unless all streams have same sizes
(define (stream-map proc . xs)
  (if (null? xs) (stream) ; returns empty stream, no second argument provided
    ; else
    (if ((car xs) 'null?) ; All streams should have same size. Testing first.
      (stream)            ; empty stream
      ; else
      (let ((heads (map (lambda (s) (s 'car)) xs)))
        (stream-cons (apply proc heads)
                     ; do not attempt to pre-calculate part of the following 
                     ; line with a 'let' statement to make the code more readable,
                     ; as this would defeat the purpose of lazy evaluation 
                     ; embedded in 'stream-cons' and introduce a nasty bug. duh!
                     (apply stream-map 
                            (cons proc (map (lambda (s) (s 'cdr)) xs))))))))

(define (stream->list s)  ; will fail badly if stream is infinite
  (if (s 'null?)
    '()
    (cons (s 'car) (stream->list (s 'cdr)))))

; a first possible definition of the fibonacci stream
(define fibs1
  (let fibgen ((a 0) (b 1))
    (stream-cons a (fibgen b (+ a b)))))

; a second possible definition of the fibonacci stream
(define fibs2 (stream-cons 0 (stream-cons 1 (stream-map + fibs2 (fibs2 'cdr)))))


