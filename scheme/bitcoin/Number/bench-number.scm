(load "bench-abstract.scm")
(load "number")

(define bench-number
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'run) (run data))
              (else (error "bench-number: unknown instance member" m)))))
    ;
    (define (run data)
      (log-message "Number benchmark running ...")
      (let ((all #t))
        (bench-from-bytes)
        (bench-to-bytes)
        (bench-add)
        (bench-mul)
        (bench-negate)
        (bench-to-string)
        (bench-random)
        (if all 
          (begin
            (bench-zero)
            (bench-one)
            (bench-sign)
            (bench-compare-to)
            (bench-hash)
            (bench-number-equals)
            (bench-from-integer)
            (bench-to-integer)
            (bench-bit-length)))))

    (define (bench-zero)
      (benchmark (lambda () (number 'zero)) "zero" 1000000)
      (benchmark (lambda () 0 'done) "zero*" 1000000))

    (define (bench-one)
      (benchmark (lambda () (number 'one)) "one" 1000000)
      (benchmark (lambda () 1 'done) "one*" 1000000))

    (define (bench-from-bytes)
      (let ((bs (get-random-bytes 32)))
        (benchmark 
          (lambda () (number 'from-bytes 1 bs) (number 'from-bytes -1 bs))
           "from-bytes (10k)" 10000) 
        (benchmark
          (lambda () (bytes->integer bs 32) (bytes->integer bs 32))
          "from-bytes* (10k)" 10000)))

    (define (bench-to-bytes)
      (let ((x (number 'random 256)))
        (let ((y (x 'negate)))
          (let ((n (x 'to-integer)) (m (y 'to-integer)))
            (benchmark
              (lambda () (x 'to-bytes 32) (y 'to-bytes 32))
              "to-bytes (10k)" 10000)
            (benchmark
              (lambda () (integer->bytes n 32) (integer->bytes m 32))
              "to-bytes* (10k)" 10000)))))

    (define (bench-add)
      (let ((x (number 'random 256)) (y ((number 'random 256) 'negate)))
        (let ((n (x 'to-integer)) (m (y 'to-integer)))
          (benchmark (lambda () (x 'add y) (y 'add x)) "add (10k)" 10000)
          (benchmark (lambda () (+ n m) (+ m n)) "add* (10k)" 10000))))

    (define (bench-mul)
      (let ((x (number 'random 256)) (y ((number 'random 256) 'negate)))
        (let ((n (x 'to-integer)) (m (y 'to-integer)))
          (benchmark (lambda () (x 'mul y) (y 'mul x)) "mul (10k)" 10000)
          (benchmark (lambda () (* n m) (* m n)) "mul* (10k)" 10000))))

    (define (bench-negate)
      (let ((x (number 'random 256)) (y ((number 'random 256) 'negate)))
        (let ((n (x 'to-integer)) (m (y 'to-integer)))
          (benchmark (lambda () (x 'negate) (y 'negate)) "negate (10k)" 10000)
          (benchmark (lambda () (- n) (- m)) "negate* (10k)" 10000))))

    (define (bench-to-string)
      (let ((x (number 'random 256)))
        (let ((y (x 'negate)))
          (let ((n (x 'to-integer)) (m (y 'to-integer)))
            (benchmark 
              (lambda () (x 'to-string) (y 'to-string)) 
              "to-string (10k)" 10000)
            (benchmark 
              (lambda () (object->string n) (object->string m)) 
                "to-string* (10k)" 10000)))))

    (define (bench-random)
      (benchmark (lambda() (number 'random 256)) "random (10k)" 10000))

    (define (bench-sign)
      (let ((x (number 'random 256)))
        (let ((y (x 'negate)))
          (let ((n (x 'to-integer)) (m (y 'to-integer)))
            (benchmark (lambda () (x 'sign) (y 'sign)) "sign" 1000000)))))

    (define (bench-compare-to)
      (let ((x (number 'random 256)) (y (number 'random 256)))
        (let ((n (x 'to-integer)) (m (y 'to-integer)))
          (benchmark 
            (lambda () (x 'compare-to y) (y 'compare-to x))
            "compare-to" 1000000)
          (benchmark 
            (lambda () (if (< n m) -1 1) (if (< m n) -1 1))
            "compare-to*" 1000000))))

    (define (bench-hash)
      (let ((x (number 'random 256)))
        (let ((n (x 'to-integer)))
          (benchmark (lambda () (x 'hash)) "hash" 1000000)
          (benchmark (lambda () (hash n 1000000000)) "hash*" 1000000))))


    (define (bench-number-equals) 'TODO)
    (define (bench-from-integer) 'TODO)
    (define (bench-to-integer) 'TODO)
    (define (bench-bit-length) 'TODO)

    ; returning no argument constructor
    (lambda ()
      (bench-abstract 'new (this #f)))))  ; bench object has no meaningful data

(define bench (bench-number))
 
(bench 'run)


(exit 0)
