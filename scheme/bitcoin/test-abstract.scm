(load "rand.scm")

(define test-abstract
  (let ()
    ; object created from data is message pasing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'run) (run data))
              ((eq? m 'self) (self data))
              (else (error "test-abstract: unknown instance member" m)))))
    ;
    ; static data
    (define generator (rand 'new))
    ;
    ; static interface
    (define (static m . args)
      (cond ((eq? m 'new) (apply new args))
            ((eq? m 'generator) generator)
            (else (error "test-abstract: unknown static member" m))))
    ;
    (define (self data) (cadr data))  ; concrete object
    ;
    (define (run data)
      (let ((self (self data)))
        (if (equal? #f self)
          (error "test-abstract: run method is abstract")
          (self 'run))))  ; running concrete method
    ;
    (define (new self) (this (list 'data self)))
    ;
    ; returning static interface
    static))

(define (get-random-bytes num-bytes)
  ((test-abstract 'generator) 'get-random-bytes num-bytes))

(define (log-message message)
  (let ((message (string-append message "\n")))
    (let ((len (string-length message)))
      (let ((bytes (string->bytes message)) (stderr (current-error-port)))
        (write-bytes bytes len stderr)))))

; optional argument to override equality predicate
; if equality predicate is overridden, function assumes
; that objects being compared have a 'to-string method
(define (check-equals left right message . args)
  (let ((predicate (if (null? args) equal? (car args)))
        (show (if (null? args) object->string (lambda (x) (x 'to-string)))))
    (if (not (predicate left right))
      (begin
        (log-message (string-append message ": check-equals failure"))
        (log-message (string-append "left = " (show left)))
        (log-message (string-append "right = " (show right)))
        (exit 1)))))

(define (check-condition condition message)
  (if (not condition)
    (begin
      (log-message (string-append message ": check-condition failure"))
      (exit 1))))







