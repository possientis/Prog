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
            ((eq? m 'debug) data) ; exposing private data for debugging
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
        (begin
        (display "-------------------------\n")
        (display "Intializing stream object\n")
        (display "data is set to cons of:\n")
        (display "1. ")(display (car args))(newline)
        (display "2. ")(display (cadr args))(newline)
        (display "-------------------------\n")
        (set! data (cons (car args) (cadr args)))))
      )
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

; simple (single stream implementation)
(define (stream-map1 proc s)
  (if (s 'null?)
    s           ; empty stream
    (stream-cons (proc (s 'car)) (stream-map1 proc (s 'cdr)))))

; general implementation
; proc requires n-arguments. xs is a list of n streams
; no sensible results unless all streams have same sizes
(define global-count 0)
(define (stream-map proc . xs)
  (set! global-count (+ global-count 1))
  (if (>= global-count 10) (exit))
  (if (null? xs) (stream) ; returns empty stream, no second argument provided
    ; else
    (if ((car xs) 'null?) ; All streams should have same size. Testing first.
      (stream)            ; empty stream
      ; else
      (begin
        (display "debug start:\n")
        (let ((heads (map (lambda (s) (s 'car)) xs)))
          (display "I am here after heads\n")
          (display "heads = ")(display heads)(newline)
          (display "xs = (x1 x2) where\n")
          (display "x1 = ")(if(eq? ones(car xs))(display "ones\n")(display "?\n"))
          (display "x2 = ")(if(eq? test(cadr xs))(display "test\n")(display "?\n"))
          (let ((tails (map (lambda (s) (s 'cdr)) xs)))
          (display "I am here\n")
          (stream-cons (apply proc heads)
                       (apply stream-map (cons proc tails)))))))))

(define (stream->list s)  ; will fail badly if stream is infinite
  (if (s 'null?)
    '()
    (cons (s 'car) (stream->list (s 'cdr)))))


; testing code for stream-map with empty stream and higher dim
; define fibonacci stream with stream-map and +

;(define fibs1
;  (let fibgen ((a 0) (b 1))
;    (stream-cons a (fibgen b (+ a b)))))

; this currently fails
;(define fibs2 (stream-cons 0 (stream-cons 1 (stream-map + fibs2 (fibs2 'cdr)))))



;(define twos (stream-map + ones ones))
; this currently fails

(define ones (stream-cons 1 ones))
(define test (stream 0 (delay (stream-map + ones test))))
(define data (cdr (test 'debug)))
(define data2 (delay (stream-map + ones test)))
(define (proc) (stream-map + ones test))
(stream-map + ones test)

