(require 'object->string)
(require 'byte-number)

(define number1
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'value) (value data))
              ((eq? m 'to-string) (to-string data))
              ((eq? m 'add) (add data))
              ((eq? m 'mul) (mul data))
              ((eq? m 'negate) (negate data))
              ((eq? m 'compare-to) (compare-to data))
              ((eq? m 'hash) (hash-code data))
              ((eq? m 'sign) (sign data))
              ((eq? m 'to-bytes) (to-bytes data))
              (else (error "number1: unknown instance member" m)))))
    ; static interface
    (define (static m)
      (cond ((eq? m 'zero) (zero))
            ((eq? m 'one) (one))
            (else (error "number1: unknown static member" m))))
    ;
    (define (zero) (number1 0))
    ;
    (define (one) (number1 1))
    ;
    (define (value data) (cadr data))
    ;
    (define (to-string data) (object->string (cadr data)))
    ;
    (define (add data) (lambda (y) (number1 (+ (cadr data) (y 'value)))))
    ;
    (define (mul data) (lambda (y) (number1 (* (cadr data) (y 'value)))))
    ;
    (define (negate data) (number1 (- (cadr data))))
    ;
    (define (compare-to data)
      (lambda (obj)
        (let ((x (cadr data)) (y (obj 'value)))
          (cond ((eq? x y)  0)
                ((< x y)   -1)
                ((> x y)    1)
                (else (error "number1: unexpected error in compare-to"))))))
    ;
    (define (hash-code data) (hash data 1000000000))
    ;
    (define (sign data)
      (let ((x (cadr data)))
        (cond ((eq? x 0) 0)
              ((< x 0)  -1)
              ((> x 0)   1)
              (else (error "number1: unexpected error in sign")))))
    ;
    (define (to-bytes data)
      (lambda (num-bytes)
        (let ((x (cadr data)))
          (if (< x 0)
            (integer->bytes (- x) num-bytes)
            (integer->bytes x num-bytes)))))

    ; returning single argument function
    (lambda (m) (if (symbol? m) (static m) (this (list 'data m))))))








