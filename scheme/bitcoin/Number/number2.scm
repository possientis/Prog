; this is essentially the same implementaion as number1.scm, with some
; optimization in the code, achieved at the cost of ugliness and lesser
; readability. This is the issue with interpreters: optimization of the 
; code changes the way the code looks.

(load "rand.scm")
(require 'object->string)
(require 'byte-number)

(define number2
  (let ((generator (rand 'new)) (zero #f) (one #f))
    ; object created from data is message passing interface
    (define (this data) 
      (lambda (m . args)
        (cond ((eq? m 'to-integer) data)
              ((eq? m 'sign) (if (< data 0) -1 (if (> data 0) 1 0)))
              ((eq? m 'compare-to) 
               (let ((y ((car args) 'to-integer)))
                (if (< data y) -1
                  (if (> data y) 1 0))))
              ((eq? m 'equal?) 
               (let ((y ((car args) 'to-integer))) (equal? data y)))
              ((eq? m 'hash) (hash data 1000000000))
              ((eq? m 'to-string) (object->string data))
              ((eq? m 'add)
               (let ((y ((car args) 'to-integer))) (this (+ data y))))
              ((eq? m 'mul)
               (let ((y ((car args) 'to-integer))) (this (* data y))))
              ((eq? m 'negate) (this (- data)))
              ((eq? m 'to-bytes) 
               (let ((num-bytes (car args)))
                 (if (< data 0)
                   (integer->bytes (- data) num-bytes)
                   (integer->bytes data num-bytes))))
              ((eq? m 'bit-length)
               (if (< data 0)
                 (integer-length (- data))
                 (integer-length data)))
              ;
              (else (error "number2: unknown instance member" m)))))
    ; static interface
    (define (static m . args)
      (cond ((eq? m 'equal?) number-equal?) 
            ((eq? m 'zero) zero)
            ((eq? m 'one) one)
            ((eq? m 'from-integer) (this (car args)))
            ((eq? m 'from-bytes) (apply from-bytes args))
            ((eq? m 'random) (apply random args))
            (else (error "number2: unknown static member" m))))
    ;
    (define (from-bytes sign bytes)
      (let ((count (bytes-length bytes)))
        (let ((value (bytes->integer bytes count)))
          (if (< sign 0)
            (this (- value))
            (this value)))))
    ;
    (define (number-equal? lhs rhs)
      (equal? (lhs 'to-integer) (rhs 'to-integer)))
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




