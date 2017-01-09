(load "test-abstract.scm")

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
      (check-to-string)
      (check-compare-to)
      (check-hash)
      (check-number-equals)
      (check-from-integer)
      (check-to-integer)
      (check-bit-length))
    ;


    (define (check-zero) 'TODO)
    (define (check-one) 'TODO)
    (define (check-from-bytes) 'TODO)
    (define (check-sign) 'TODO)
    (define (check-to-bytes) 'TODO)
    (define (check-random) 'TODO)
    (define (check-add) 'TODO)
    (define (check-mul) 'TODO)
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

