(load "test-abstract.scm")
(load "number")

(define test-number
  (let () 
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'run) (run data))
              (else (error "test-number: unknown instance member" m)))))
    ;
    (define (run data)
      (log-message "Number unit test running ...")
      (check-zero)
      (check-one)
      (check-from-bytes)
      (check-sign)
      (check-to-bytes)
      (check-random)
      (check-add)
      (check-mul)
      (check-negate)
      (check-to-string)
      (check-compare-to)
      (check-hash)
      (check-number-equals)
      (check-from-integer)
      (check-to-integer)
      (check-bit-length))
    ;
    ; helper function
    (define (signed-random num-bits)
      (let ((x (number 'random num-bits)) (flip (number 'random 1)))
        (if (flip 'equal? (number 'one))
          (x 'negate)
          x)))
    ;
    ; syntactic sugar
    (define (check-num-equals lhs rhs message)
      (check-equals lhs rhs message (number 'equal?)))

    ;
    (define (check-zero)
      (let ((zero (number 'zero)) (x (number 'random 256)))
        (let ((y (zero 'add x)) (z (x 'add zero)))
          (check-num-equals x y "check-zero.1")
          (check-num-equals x z "check-zero.2" ))))
    ;
    (define (check-one)
      (let ((one (number 'one)) (x (number 'random 256)))
        (let ((y (one 'mul x)) (z (x 'mul one)))
          (check-num-equals x y "check-one.1" )
          (check-num-equals x z "check-one.2" ))))
    ;
    (define (check-from-bytes)
      ; empty byte string
      (let ((b0 (list->bytes '())))
        (let ((x (number 'from-bytes 1 b0)))
          (check-num-equals x (number 'zero) "check-from-bytes.1"))
        (let ((x (number 'from-bytes -1 b0)))
          (check-num-equals x (number 'zero) "check-from-bytes.2"))
        (let ((x (number 'from-bytes 0 b0)))
          (check-num-equals x (number 'zero) "check-from-bytes.3")))

      ; single #x00 byte
      (let ((b1 (list->bytes '(#x00))))
        (let ((x (number 'from-bytes 1 b1)))
          (check-num-equals x (number 'zero) "check-from-bytes.6"))
        (let ((x (number 'from-bytes -1 b1)))
          (check-num-equals x (number 'zero) "check-from-bytes.7"))
        (let ((x (number 'from-bytes 0 b1)))
          (check-num-equals x (number 'zero) "check-from-bytes.8")))

      ; two #x00 bytes
      (let ((b2 (list->bytes '(#x00 #x00))))
        (let ((x (number 'from-bytes 1 b2)))
          (check-num-equals x (number 'zero) "check-from-bytes.11"))
        (let ((x (number 'from-bytes -1 b2)))
          (check-num-equals x (number 'zero) "check-from-bytes.12"))
        (let ((x (number 'from-bytes 0 b2)))
          (check-num-equals x (number 'zero) "check-from-bytes.13")))

      ; single #x01 byte
      (let ((b3 (list->bytes '(#x01))))
        (let ((x (number 'from-bytes 1 b3)))
          (check-num-equals x (number 'one) "check-from-bytes.16")))

      ; x + (-x) = 0
      (let ((b4 (get-random-bytes 32)))
        (let ((x (number 'from-bytes 1 b4)) (y (number 'from-bytes -1 b4)))
          (let ((z (x 'add y)))
            (check-num-equals z (number 'zero) "check-from-bytes.18"))))

      ; multiplying by -1
      (let ((b3 (list->bytes '(#x01))))
        (let ((b4 (get-random-bytes 32)) (z (number 'from-bytes -1 b3)))
          (let ((x (number 'from-bytes 1 b4)) (y (number 'from-bytes -1 b4)))
            (check-num-equals y (x 'mul z) "check-from-bytes.19"))))

      ; padding with #x00 bytes
      (let ((b5 (get-random-bytes 28)))
        (let ((x (number 'from-bytes 1 b5)) (y (number 'from-bytes -1 b5)))
          (let ((b6 (list->bytes
                      (cons #x00
                            (cons #x00
                                  (cons #x00
                                        (cons #x00 (bytes->list b5))))))))
            (let ((z (number 'from-bytes 1 b6)))
              (check-num-equals x z "check-from-bytes.20"))
            (let ((z (number 'from-bytes -1 b6)))
              (check-num-equals y z "check-from-bytes.21"))))) 

      ; actual replication
      (let ((b7 (get-random-bytes 32)) (b8 (make-bytes 1 #xff))) ; b8 = 255
        (let ((_256 ((number 'from-bytes 1 b8) 'add (number 'one))))
          (let ((x (number 'from-bytes 1 b7)) (y (number 'from-bytes -1 b7)))
            (let loop ((z (number 'zero))   ; z accumulating to x
                       (t (number 'zero))   ; t accumulating to y
                       (i 0))               ; i = 0
              (if (< i 32)
                (let ((b8 (make-bytes 1 (byte-ref b7 i))))  ; b8 =[b7[i]]
                  (loop ((z 'mul _256) 'add (number 'from-bytes 1 b8))
                        ((t 'mul _256) 'add (number 'from-bytes -1 b8))
                        (+ i 1)))
                (begin  ; i = 32
                  (check-num-equals x z "check-from-bytes.22")
                  (check-num-equals y t "check-from-bytes.23")))))))

      ; using to-bytes and sign
      (let ((b9 (get-random-bytes 32)))
        (let ((x (number 'from-bytes 1 b9)) (y (number 'from-bytes -1 b9)))
          (check-equals (x 'sign) 1 "check-from-bytes.24")
          (check-equals (y 'sign)-1 "check-from-bytes.25")
          (let ((b10 (x 'to-bytes 32)) (b11 (y 'to-bytes 32)))
            (check-equals b9 b10 "check-from-bytes.26")
            (check-equals b9 b11 "check-from-bytes.27")))))

    ;
    (define (check-sign)
      (check-equals ((number 'zero) 'sign) 0 "check-sign.1")

      (let ((bs (get-random-bytes 32)))
        (let ((x (number 'from-bytes 1 bs)) (y (number 'from-bytes -1 bs)))
          (check-equals (x 'sign) 1 "check-sign.2")
          (check-equals (y 'sign)-1 "check-sign.3"))))

    ;
    (define (check-to-bytes)
      ; zero
      (let ((bs ((number 'zero) 'to-bytes 0)))
        (check-equals (bytes-length bs) 0 "check-to-bytes.0")
        (check-equals bs (make-bytes 0) "check-to-bytes.1"))
      (let ((bs ((number 'zero) 'to-bytes 32)))
        (check-equals (bytes-length bs) 32 "check-to-bytes.2")
        (let loop ((i 0))
          (if (< i 32)
            (begin
              (check-equals (byte-ref bs i) #x00 "check-to-bytes.3")
              (loop (+ i 1))))))
      ; one
      (let ((bs ((number 'one) 'to-bytes 1)))
        (check-equals (bytes-length bs) 1 "check-to-bytes.5")
        (check-equals bs (make-bytes 1 #x01) "check-to-bytes.6"))
      (let ((bs (((number 'one) 'negate) 'to-bytes 1)))
        (check-equals (bytes-length bs) 1 "check-to-bytes.7")
        (check-equals bs (make-bytes 1 #x01) "check-to-bytes.8"))
      (let ((bs ((number 'one) 'to-bytes 32)))
        (check-equals (bytes-length bs) 32 "check-to-bytes.9")
        (check-equals (byte-ref bs 31) #x01 "check-to-bytes.10")  ; big-endian
        (let loop ((i 0))
          (if (< i 31)  ; only testing highest 31 bytes which should #x00
             (begin
               (check-equals (byte-ref bs i) #x00 "check-to-bytes.11")
               (loop (+ i 1))))))     ; tail recursive
      ; random
      (let ((x (number 'random 256)))
        (let ((y (x 'negate)))
          (let ((bs (x 'to-bytes 32)))
            (check-num-equals x (number 'from-bytes 1 bs) "check-to-bytes.12")
            (check-num-equals y (number 'from-bytes -1 bs) "check-to-bytes.13"))
          (let ((bs (y 'to-bytes 32)))
            (check-num-equals x (number 'from-bytes 1 bs) "check-to-bytes.14")
            (check-num-equals y (number 'from-bytes -1 bs) "check-to-bytes.15")))))
    ;
    (define (check-random)
      ; checking a random generator should be far more
      ; involved than anything done here
      (let ((x (number 'random 0))) ; zero bit number, has to be 0
        (check-num-equals x (number 'zero) "check-random.1"))
      (let ((x (number 'random 1))) ; single bit
        (check-condition
          (or (x 'equal? (number 'zero)) (x 'equal? (number 'one)))
          "check-random.2"))
      (let ((x (number 'random 256))) ; generates non-negative number
        (check-equals (x 'sign) 1 "check-random.3"))

      ; this loop seems to be abnormally slow. TODO: investigate
      (let loop ((i 0) (count 0))
        (if (< i 10000)
          (let ((x (number 'random 256)))
            (let ((bs (x 'to-bytes 32)))
              (let ((y (number 'random 5)))   ; selecting byte 0 to 31
                (let ((index (y 'to-integer)))
                  (let ((test (byte-ref bs index)))
                    (let ((z (number 'random 3))) ; selecting bit 0 to 7
                      (let ((bit (z 'to-integer))); testing 'bit' of 'test'
                        (if (equal? 1 (logand (ash test (- bit)) #x01))
                          (loop (+ i 1) (+ count 1))    ; bit is set
                          (loop (+ i 1) count)))))))))  ; bit is not set 
          ; i = 10000
          (begin
            (check-condition (> count 4800) "check-random.4")
            (check-condition (< count 5200) "check-random.5")))))

    ;
    (define (check-add)
      (let ((x (signed-random 256)) 
            (y (signed-random 256)) 
            (z (signed-random 256)))
        ; x + 0 = x
        (check-num-equals (x 'add (number 'zero)) x "check-add.1")
        ; 0 + x = x
        (check-num-equals ((number 'zero) 'add x) x "check-add.2")
        ; x + (-x) = 0
        (check-num-equals (x 'add (x 'negate)) (number 'zero) "check-add.3")
        ; (-x) + x = 0
        (check-num-equals ((x 'negate) 'add x) (number 'zero) "check-add.4")
        ; x + y = y + x
        (check-num-equals (x 'add y) (y 'add x) "check-add.5")
        ; (x + y) + z = x + (y + z)
        (check-num-equals ((x 'add y) 'add z) (x 'add (y 'add z)) "check-add.6")
        ; actual check of x + y
        (let ((n (x 'to-integer)) (m (y 'to-integer)))
          (let ((check (number 'from-integer (+ n m))))
            (check-num-equals check (x 'add y) "check-add.7")))))

    ;
    (define (check-mul)
      (let ((x (signed-random 256)) 
            (y (signed-random 256)) 
            (z (signed-random 256)))
        ; x * 0 = 0
        (check-num-equals (x 'mul (number 'zero)) (number 'zero) "check-mul.1")
        ; 0 * x = 0
        (check-num-equals ((number 'zero) 'mul x) (number 'zero) "check-mul.2")
        ; x * 1 = x
        (check-num-equals (x 'mul (number 'one)) x "check-mul.3")
        ; 1 * x = x
        (check-num-equals ((number 'one) 'mul x) x "check-mul.4")
        ; (-x) * (-y) = x * y
        (check-num-equals ((x 'negate) 'mul (y 'negate)) (x 'mul y) "check-mul.5")
        ; x * y = y * x
        (check-num-equals (x 'mul y) (y 'mul x) "check-mul.6")
        ; (x * y) * z = x * (y * z)
        (check-num-equals ((x 'mul y) 'mul z) (x 'mul (y 'mul z)) "check-mul.7")
        ; (x + y) * z = (x * z) + (y * z)
        (check-num-equals 
          ((x 'add y) 'mul z) ((x 'mul z) 'add (y 'mul z)) "check-mul.8")
        ; actual check of x * y
        (let ((n (x 'to-integer)) (m (y 'to-integer)))
          (let ((check (number 'from-integer (* n m))))
            (check-num-equals check (x 'mul y) "check-mul.9")))))

    ;
    (define (check-negate)
      (let ((x (signed-random 256)))
        (let ((y (x 'negate)))
          ; x + (-x) = 0
          (check-num-equals (number 'zero) (x 'add y) "check-negate.1")
          ; acual check
          (let ((n (x 'to-integer)))
            (let ((check (number 'from-integer (- n))))
              (check-num-equals check y "check-negate.2"))))))

    ;
    (define (check-to-string)
      ; zero
      (let ((check1 ((number 'zero) 'to-string)))
        (check-equals check1 "0" "check-to-string.1"))
      ; one
      (let ((check1 ((number 'one) 'to-string)))
        (check-equals check1 "1" "check-to-string.2"))
      ; minus one
      (let ((check1 (((number 'one) 'negate) 'to-string)))
        (check-equals check1 "-1" "check-to-string.3"))
      ; random positive
      (let ((x (number 'random 256)))
        (let ((check1 (x 'to-string)) 
              (check2 (object->string (x 'to-integer))))
          (check-equals check1 check2 "check-to-string.4"))))

    ;
    (define (check-compare-to)
      ; from random
      (let ((x (number 'random 256)))
        (let ((y (x 'negate)))
          (check-equals (x 'compare-to (number 'zero)) 1 "check-compare-to.1")
          (check-equals ((number 'zero) 'compare-to x) -1 "check-compare-to.2")
          (check-equals (y 'compare-to (number 'zero)) -1 "check-compare-to.3")
          (check-equals ((number 'zero) 'compare-to y) 1 "check-compare-to.4")))
      ; from bytes
      (let ((bs (get-random-bytes 32)))
        (let ((x (number 'from-bytes 1 bs)) (y (number 'from-bytes -1 bs)))
          (check-equals (x 'compare-to (number 'zero)) 1 "check-compare-to.5")
          (check-equals ((number 'zero) 'compare-to x) -1 "check-compare-to.6") 
          (check-equals (y 'compare-to (number 'zero)) -1 "check-compare-to.7")
          (check-equals ((number 'zero) 'compare-to y) 1 "check-compare-to.8")))
      ; from signed-random
      (let ((x (signed-random 256)) (y (signed-random 256)))
        (let ((n (x 'to-integer)) (m (y 'to-integer)))
          (check-equals (x 'compare-to y) (if (< n m) -1 1) "check-compare-to.9")
          (check-equals (y 'compare-to x) (if (< n m) 1 -1) "check-compare-to.10")
          (let ((z (number 'from-integer n))) ; x = z
            (check-equals (x 'compare-to z) 0 "check-compare-to.11")
            (check-equals (z 'compare-to x) 0 "check-compare-to.12"))))
      ; 0 < 1
      (check-equals 
        ((number 'zero) 'compare-to (number 'one)) -1 "check-compare-to.13")
      (check-equals
        ((number 'one) 'compare-to (number 'zero)) 1 "check-compare-to.14"))

    ;
    (define (check-hash)
      ; 0 and 1
      (let ((hash1 ((number 'zero) 'hash)) (hash2 ((number 'one) 'hash)))
        (check-condition (not (equal? hash1 hash2)) "check-hash.1"))
      ; x and -x
      (let ((x (signed-random 256)))
        (let ((hash1 (x 'hash)) (hash2 ((x 'negate) 'hash)))
          (check-condition (not (equal? hash1 hash2)) "check-hash.2")))
      ; same number
      (let ((x (signed-random 256)))
        (let ((n (x 'to-integer)))
          (let ((y (number 'from-integer n)))
            (let ((hash1 (x 'hash)) (hash2 (y 'hash)))
              (check-equals hash1 hash2 "check-hash.3"))))))

    ;
    (define (check-number-equals)
      ; 0 and 1
      ; static member
      (check-condition
        (not ((number 'equal?) (number 'zero) (number 'one))) 
        "check-number-equals.1")
      (check-condition  
        (not ((number 'equal?) (number 'one) (number 'zero))) 
        "check-number-equals.2")
      ; instance member
      (check-condition  
        (not ((number 'zero) 'equal? (number 'one))) 
        "check-number-equals.3")
      (check-condition  
        (not ((number 'one) 'equal? (number 'zero))) 
        "check-number-equals.4")

      ; x and -x
      (let ((x (signed-random 256)))
        ; static member
        (check-condition  
          (not ((number 'equal?) x (x 'negate))) "check-number-equals.5")
        (check-condition  
          (not ((number 'equal?) (x 'negate) x)) "check-number-equals.6")
        ; instance member
        (check-condition  
          (not (x 'equal? (x 'negate))) "check-number-equals.7")
        (check-condition 
          (not ((x 'negate) 'equal? x)) "check-number-equals.8"))

      ; same number
      (let ((x (signed-random 256)))
        (let ((n (x 'to-integer)))
          (let ((y (number 'from-integer n)))
            ; static member
            (check-condition ((number 'equal?) x y) "check-number-equals.9")
            (check-condition ((number 'equal?) y x) "check-number-equals.10")
            (check-condition ((number 'equal?) x x) "check-number-equals.11")
            ; instance member
            (check-condition (x 'equal? y) "check-number-equals.12")
            (check-condition (y 'equal? x) "check-number-equals.13")
            (check-condition (x 'equal? x) "check-number-equals.14")
            ; checking check-num-equals
            (check-num-equals x y "check-number-equals.15")
            (check-num-equals y x "check-number-equals.16")
            (check-num-equals x x "check-number-equals.17")))))

    ;
    (define (check-from-integer)
      ; 0
      (let ((x (number 'from-integer 0)) (y (number 'zero)))
        (check-num-equals x y "check-from-integer.1"))
      ;1
      (let ((x (number 'from-integer 1)) (y (number 'one)))
        (check-num-equals x y "check-from-integer.2"))

      ; signed-random
      (let ((x (signed-random 256)))
        (let ((y (number 'from-integer (x 'to-integer))))
          (check-num-equals x y "check-from-integer.3"))))

    ;
    (define (check-to-integer)
      ; 0
      (let ((n ((number 'zero) 'to-integer)))
        (check-equals n 0 "check-to-integer.1"))
      ; 1
      (let ((n ((number 'one) 'to-integer)))
        (check-equals n 1 "check-to-integer.2"))

      ; signed-random
      (let ((x (signed-random 256)))
        (let ((n (x 'to-integer)))
          (let ((m (bytes->integer (x 'to-bytes 32) 32)))
            (let ((p (if (equal? 1 (x 'sign)) m (- m))))
              (check-equals n p "check-to-integer.3"))))))

    ;
    (define (check-bit-length)
      ; 0
      (let ((check1 ((number 'zero) 'bit-length)))
        (check-equals check1 0 "check-bit-length.1"))
      ; 1
      (let ((check1 ((number 'one) 'bit-length)))
        (check-equals check1 1 "check-bit-length.2"))
      ; -1
      (let ((check1 (((number 'one) 'negate) 'bit-length)))
        (check-equals check1 1 "check-bit-length.3"))
      ;
      (let ((_2 ((number 'one) 'add (number 'one))))
        (let ((_4 (_2 'mul _2)))
          (let ((_16 (_4 'mul _4)))
            (let ((_256 (_16 'mul _16)))
              ; 2
              (let ((check1 (_2 'bit-length)))
                (check-equals check1 2 "check-bit-length.4"))
              ; -2
              (let ((check1 ((_2 'negate) 'bit-length)))
                (check-equals check1 2 "check-bit-length.5"))
              ; 4
              (let ((check1 (_4 'bit-length)))
                (check-equals check1 3 "check-bit-length.6"))
              ; -4
              (let ((check1 ((_4 'negate) 'bit-length)))
                (check-equals check1 3 "check-bit-length.7"))
              ; 16 
              (let ((check1 (_16 'bit-length)))
                (check-equals check1 5 "check-bit-length.8"))
              ; -16
              (let ((check1 ((_16 'negate) 'bit-length)))
                (check-equals check1 5 "check-bit-length.9"))
              ; 256 
              (let ((check1 (_256 'bit-length)))
                (check-equals check1 9 "check-bit-length.10"))
              ; -256
              (let ((check1 ((_256 'negate) 'bit-length)))
                (check-equals check1 9 "check-bit-length.11"))))))
      ; +- 2^256
      (let ((bs (make-bytes 33 #x00)))
        (byte-set! bs 0 #x01) ; high-order byte set to #x01
        (let ((x (number 'from-bytes 1 bs)) (y (number 'from-bytes -1 bs)))
          (check-equals (x 'bit-length) 257 "check-bit-length.12")
          (check-equals (y 'bit-length) 257 "check-bit-length.13"))))
    ;
    ; returning no argument constructor
    (lambda ()
      (test-abstract 'new (this #f)))))   ; test object has no meaningful data

(define test (test-number))

(test 'run)

(exit 0)
