(load "rand.scm")
(require 'object->string)
(require 'byte-number)

(define number2
  (let ((generator (rand 'new)))
    ; object created from data is message passing interface
    (define this 
      (lambda (data)
        (lambda (m . args)
          (cond ((eq? m 'to-integer) (cadr data))
                ((eq? m 'compare-to) (apply (compare-to data) args))
                ((eq? m 'hash) (hash data 1000000))
                ((eq? m 'to-string) (to-string data))
                ((eq? m 'add) (apply (add data) args))
                ((eq? m 'mul) (apply (mul data) args))
                ((eq? m 'negate) (this (list 'data (- (cadr data)))))
                ((eq? m 'equal?) (apply (equal-to data) args))
                ((eq? m 'to-bytes) (apply (to-bytes data) args))
                ((eq? m 'bit-length) (bit-length data))
                ((eq? m 'sign) (sign data))
                (else (error "number2: unknown instance member" m))))))
    ; static interface
    (define static 
      (lambda (m . args)
        (cond ((eq? m 'zero) (this (list 'data 0)))
              ((eq? m 'one) (this (list 'data 1)))
              ((eq? m 'from-integer) (this (list 'data (car args))))
              ((eq? m 'from-bytes) (apply from-bytes args))
              ((eq? m 'random) (apply random args))
              ((eq? m 'equal?) number-equal?) 
              (else (error "number2: unknown static member" m)))))
    ;
    (define (from-bytes sign bytes)
      (let ((count (bytes-length bytes)))
        (let ((value (bytes->integer bytes count)))
          (if (< sign 0)
            (this (list 'data (- value)))
            (this (list 'data value))))))
    ;
    (define (to-string data) (object->string (cadr data)))
    ;
    (define (add data) 
      (lambda (obj) 
        (let ((x (cadr data)) (y (obj 'to-integer)))
          (this (list 'data (+ x y))))))
    ;
    (define (mul data) 
      (lambda (obj)
        (let ((x (cadr data)) (y (obj 'to-integer)))
          (this (list 'data (* x y))))))
    ;
    (define (compare-to data)
      (lambda (lhs)
        (let ((x (cadr data)) (y (lhs 'to-integer)))
          (cond ((< x y) -1)
                ((> x y)  1)
                (else     0)))))
;                (else (error "number2: unexpected error in compare-to"))))))
    ;
    (define (equal-to data)
      (lambda (lhs)
        (let ((x (cadr data)) (y (lhs 'to-integer)))
          (equal? x y))))
    ;
    (define (number-equal? lhs rhs)
      (equal? (lhs 'to-integer) (rhs 'to-integer)))
    ;
    (define (sign data)
      (let ((x (cadr data)))
        (cond ((equal? x 0) 0)
              ((< x 0)  -1)
              ((> x 0)   1)
              (else (error "number2: unexpected error in sign")))))
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
    ;
    (define (random num-bits)
        (from-bytes 1 (random-bytes num-bits)))  
    ;
    ; Returns unsigned random number as big-endian bytes.
    ; Essentially generates random bytes and subsequently 
    ; set the appropriate number of leading bits to 0 so 
    ; as to ensure the final bytes have the right bit size
    ;
    (define (random-bytes num-bits)
      (let ((len (quotient (+ num-bits 7) 8)))  ; number of bytes required
        (if (equal? 0 len)
          (make-bytes 0)                        ; returning empty byte-string
          (let ((bytes (generator 'get-random-bytes len)))
            (let ((lead (byte-ref bytes 0))     ; high order byte
                  (diff (- (* len 8) num-bits))); number of leading bits set to 0
              (let ((front (shave diff lead)))  ; new leading byte
                (byte-set! bytes 0 front)
                bytes))))))
                  
    ;
    ; return byte with n leading bits set to 0
    (define (shave n byte)
      (let loop ((mask #x7f) (n n) (byte byte))
        (if (equal? n 0)
          byte
          (loop (ash mask -1) (- n 1) (logand byte mask)))))

    ; returning static interface
    static))




