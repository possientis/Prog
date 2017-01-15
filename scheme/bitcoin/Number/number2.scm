(load "rand.scm")
(require 'object->string)
(require 'byte-number)

(define number2
  (let ((generator (rand 'new)) (zero #f) (one #f))
    ; object created from data is message passing interface
    (define this 
      (lambda (data)
        (lambda (m . args)
          (cond ((eq? m 'to-integer) data)
                ((eq? m 'compare-to) (apply (compare-to data) args))
                ((eq? m 'hash) (hash data 1000000000))
                ((eq? m 'to-string) (to-string data))
                ((eq? m 'add) (apply (add data) args))
                ((eq? m 'mul) (apply (mul data) args))
                ((eq? m 'negate) (this (- data)))
                ((eq? m 'equal?) (apply (equal-to data) args))
                ((eq? m 'to-bytes) (apply (to-bytes data) args))
                ((eq? m 'bit-length) (bit-length data))
                ((eq? m 'sign) (sign data))
                (else (error "number2: unknown instance member" m))))))
    ; static interface
    (define static 
      (lambda (m . args)
        (cond ((eq? m 'zero) zero)
              ((eq? m 'one) one)
              ((eq? m 'from-integer) (this (car args)))
              ((eq? m 'from-bytes) (apply from-bytes args))
              ((eq? m 'random) (apply random args))
              ((eq? m 'equal?) number-equal?) 
              (else (error "number2: unknown static member" m)))))
    ;
    (define (from-bytes sign bytes)
      (let ((count (bytes-length bytes)))
        (let ((value (bytes->integer bytes count)))
          (if (< sign 0)
            (this (- value))
            (this value)))))
    ;
    (define (to-string data) (object->string data))
    ;
    (define (add data) 
      (lambda (obj) 
        (let ((y (obj 'to-integer)))
          (this (+ data y)))))
    ;
    (define (mul data) 
      (lambda (obj)
        (let ((y (obj 'to-integer)))
          (this (* data y)))))
    ;
    (define (compare-to data)
      (lambda (lhs)
        (let ((y (lhs 'to-integer)))
          (cond ((< data y) -1)
                ((> data y)  1)
                (else     0)))))
;                (else (error "number2: unexpected error in compare-to"))))))
    ;
    (define (equal-to data)
      (lambda (lhs)
        (let ((y (lhs 'to-integer)))
          (equal? data y))))
    ;
    (define (number-equal? lhs rhs)
      (equal? (lhs 'to-integer) (rhs 'to-integer)))
    ;
    (define (sign data)
      (cond ((equal? data 0) 0)
            ((< data 0)  -1)
            ((> data 0)   1)
            (else (error "number2: unexpected error in sign"))))
    ;
    (define (to-bytes data)
      (lambda (num-bytes)
        (if (< data 0)
          (integer->bytes (- data) num-bytes)
          (integer->bytes data num-bytes))))
    ;
    (define (bit-length data)
      (if (< data 0)
        (integer-length (- data))
        (integer-length data)))
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

    ; initialization
    (set! zero (this 0))
    (set! one (this 1))
    ; returning static interface
    static))




