(load "rand.scm")
(require 'printf)

(define bench-abstract
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'run) (run data))
              ((eq? m 'self) (self data))
              (else (error "bench-abstract: unknown instance member" m)))))
    ;
    ; static data
    (define generator (rand 'new))
    ;
    ; static interface
    (define (static m . args)
      (cond ((eq? m 'new) (apply new args))
            ((eq? m 'generator) generator)
            (else (error "bench-anstract: unknown static member" m))))
    ;
    (define (self data) (cadr data))  ; concrete object 
    ;
    (define (run data)
      (let ((self (self data)))
        (if (equal? #f self)
          (error "bench-abstract: run method is abstract")
          (self 'run))))    ; running concrete method
    ;
    (define (new self) (this (list 'data self)))
    ;
    ; returning static interface
    static))


(define (get-random-bytes num-bytes)
  ((bench-abstract 'generator) 'get-random-bytes num-bytes))

(define (log-message message)
  (let ((message (string-append message "\n")))
    (let ((len (string-length message)))
      (let ((bytes (string->bytes message)) (stderr (current-error-port)))
        (write-bytes bytes len stderr)))))

(define (benchmark call-back name iterations)
  (let ((start (get-internal-run-time)))
    (let loop ((i 0))
      (if (< i iterations)
        (begin
          (call-back)
          (loop (+ i 1)))
        (let ((end (get-internal-run-time)))
          (fprintf (current-error-port) 
                   "Benchmark: %s, %d iterations ran in %.3f seconds\n" 
                   name 
                   iterations 
                   (/ (- end start) internal-time-units-per-second)))))))
  

