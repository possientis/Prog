; stream.scm
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

;; bridge
(define (stream . args) 
  (apply stream1 args)) ; can select various implementations here
;
; more efficient implementation
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

(define (stream-scale s factor)
  (stream-map (lambda (x) (* x factor)) s))

(define (stream-add s1 s2)
  (stream-map + s1 s2))

(define (stream-mul s1 s2)
  (stream-map * s1 s2))

(define (stream-partial-sums s)
  (if (s 'null?) (stream) ; empty stream
    ; else
    (let ((first (s 'car)))
      (stream-cons first
                   (stream-map
                   (lambda (x) (+ x first))
                   (stream-partial-sums (s 'cdr)))))))
(define (stream-merge s1 s2)
  (cond ((s1 'null?) s2)
        ((s2 'null?) s1)
        (else (let ((car1 (s1 'car))(car2 (s2 'car)))
                (cond ((< car1 car2)
                       (stream-cons car1 (stream-merge (s1 'cdr) s2)))
                      ((< car2 car1)
                       (stream-cons car2 (stream-merge s1 (s2 'cdr))))
                      (else ; car1 == car2
                        (stream-cons car1 (stream-merge (s1 'cdr) (s2 'cdr)))))))))

(define (stream-expand num den radix)
  (stream-cons
    (quotient (* num radix) den)
    (stream-expand (remainder (* num radix) den) den radix)))


(define (stream-interleave s1 s2)
  (if (s1 'null?) 
    s2
    (stream-cons (s1 'car)
                 (stream-interleave s2 (s1 'cdr)))))

(define (stream-upper-pairs s1 s2)
  (cond ((s1 'null?) (stream))
        ((s2 'null?) (stream))
        (else (stream-cons
                (list (s1 'car) (s2 'car))
                (stream-interleave
                  (stream-map (lambda (x) (list (s1 'car) x))
                              (s2 'cdr))
                  (stream-upper-pairs (s1 'cdr) (s2 'cdr)))))))
(define (stream-pairs s1 s2)
  (cond ((s1 'null?) (stream))
        ((s2 'null?) (stream))
        (else (stream-cons
                (list (s1 'car) (s2 'car))
                (stream-interleave
                  (stream-interleave
                    (stream-map (lambda (x) (list (s1 'car) x))
                                (s2 'cdr))
                    (stream-map (lambda (x) (list x (s2 'car)))
                                (s1 'cdr)))
                  (stream-pairs (s1 'cdr) (s2 'cdr)))))))

;; the following code fails on infinite streams. The reason is
;; the lack of 'stream-cons' to block eager evaluation.
;; So stream-upper-pairs2 calls stream-interleave which forces
;; evaluation of its second argument, trigerring a new call
;; to stream-upper-pairs2, thus creating an inifinite chain
;; of mutually recursive calls between the two functions
;
;(define (stream-upper-pairs2 s1 s2)
;  (cond ((s1 'null?) (stream))
;        ((s2 'null?) (stream))
;        (else (stream-interleave
;                (stream-map (lambda (x) (list (s1 'car) x)) s2)
;                (stream-upper-pairs2 (s1 'cdr) (s2 'cdr))))))
;                  
;(define (stream-upper-triples s1 s2 s3)
;  (cond ((s1 'null?) (stream))
;        ((s2 'null?) (stream))
;        ((s3 'null?) (stream))
;        (else (stream-cons
;                (list (s1 'car) (s2 'car) (s3 'car))
;                (stream-interleave
;                  (stream-map (lambda (x) (list (s1 'car) (s2 'car) x))
;                              (s3 'cdr))
;                  (stream-interleave
;                    (stream-map (lambda (x) (cons (s1 'car) x))
;                                (stream-upper-pairs (s2 'cdr) (s3 'cdr)))
;                    (stream-upper-triples (s1 'cdr) (s2 'cdr) (s3 'cdr))))))))
;
;(define (square x) (* x x))
;
;(define (pythagoras-triple? x)
;  (= (square (caddr x)) (+ (square (cadr x)) (square (car x)))))
;
;(define triples 
;  (let ((integers (integers-from 1)))
;    (stream-upper-triples integers integers integers)))
;
;(define pythagoras (stream-filter pythagoras-triple? triples)) 
;
;(display (stream-take 3 pythagoras))
;(newline)
;
