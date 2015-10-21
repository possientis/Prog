; stream.scm
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
    ((stream-cons expr1 expr2)        ; expr2 should return a stream object
     (stream expr1 (delay expr2)))))  ; returning stream object

; stream class
(define (stream . args) ; args = '() or args = '(expr1 (delay expr2))
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


(define (stream-ref s n)
  (if (= n 0)
    (s 'car)
    (stream-ref (s 'cdr) (- n 1))))

(define (stream-map proc s)
  (if (s 'null?)
    (stream)  ; empty stream
    (((stream) 'cons) (proc (s 'car)) (stream-map proc (s 'cdr)))))

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
    (stream)
    (stream-cons (car seq) (list->stream (cdr seq)))))

(define (stream->list s)  ; will fail badly if stream is infinite
  (if (s 'null?)
    '()
    (cons (s 'car) (stream->list (s 'cdr)))))

(define (stream-take myStream num)
  (cond ((= 0 num) '())
        ((myStream 'null?) '())
        (else (cons (myStream 'car) (stream-take (myStream 'cdr) (- num 1))))))








