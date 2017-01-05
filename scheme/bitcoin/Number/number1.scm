(require 'object->string)
(require 'byte-number)

(define number1
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m . args)
        (cond ((eq? m 'to-integer) (to-integer data))
              ((eq? m 'to-string) (to-string data))
              ((eq? m 'add) (apply (add data) args))
              ((eq? m 'mul) (apply (mul data) args))
              ((eq? m 'negate) (negate data))
              ((eq? m 'compare-to) (apply (compare-to data) args))
              ((eq? m 'hash) (hash-code data))
              ((eq? m 'sign) (sign data))
              ((eq? m 'to-bytes) (apply (to-bytes data) args))
              ((eq? m 'bit-length) (bit-length data))
              (else (error "number1: unknown instance member" m)))))
    ; static interface
    (define (static m . args)
      (cond ((eq? m 'zero) (zero))
            ((eq? m 'one) (one))
            ((eq? m 'from-integer) (apply from-integer args))
            ((eq? m 'from-bytes) (apply from-bytes args))
            (else (error "number1: unknown static member" m))))
    ;
    (define (zero) (from-integer 0))
    ;
    (define (one) (from-integer 1))
    ;
    (define (from-integer value) (this (list 'data value)))
    ;
    (define (from-bytes sign bytes)
      (let ((count (bytes-length bytes)))
        (let ((value (bytes->integer bytes count)))
          (if (< sign 0)
            (from-integer (- value))
            (from-integer value)))))
    ;
    (define (to-integer data) (cadr data))
    ;
    (define (to-string data) (object->string (cadr data)))
    ;
    (define (negate data) (from-integer (- (cadr data))))
    ;
    (define (hash-code data) (hash data 1000000000))
    ;
    (define (add data) 
      (lambda (obj) 
        (let ((x (cadr data)) (y (obj 'to-integer)))
          (from-integer (+ x y)))))
    ;
    (define (mul data) 
      (lambda (obj)
        (let ((x (cadr data)) (y (obj 'to-integer)))
          (from-integer (* x y)))))
    ;
    (define (compare-to data)
      (lambda (obj)
        (let ((x (cadr data)) (y (obj 'to-integer)))
          (cond ((eq? x y)  0)
                ((< x y)   -1)
                ((> x y)    1)
                (else (error "number1: unexpected error in compare-to"))))))
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
    ;
    (define (bit-length data)
      (let ((x (cadr data)))
        (if (< x 0)
          (integer-length (- x))
          (integer-length x))))

    ; returning static interface
    static))








