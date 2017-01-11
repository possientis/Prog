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
    (define (check-add) 'TODO)
    (define (check-mul) 'TODO)
    (define (check-negate) 'TODO)
    (define (check-to-string) 'TODO)
    (define (check-compare-to) 'TODO)
    (define (check-hash) 'TODO)
    (define (check-number-equals) 'TODO)
    (define (check-from-integer) 'TODO)
    (define (check-to-integer) 'TODO)
    (define (check-bit-length) 'TODO)

    ;
    ; returning no argument constructor
    (lambda ()
      (test-abstract 'new (this #f)))))   ; test object has no meaningful data


(define test (test-number))
(test 'run)
(exit 0)
