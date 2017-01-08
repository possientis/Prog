(require 'random)
(require 'byte)
(require 'byte-number)

(define rand1
  (let ()
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m . args)
        (cond ((eq? m 'get-random-bytes) (apply (get-random-bytes data) args))
              (else (error "random1: unknown instance member" m)))))
    ; static interface
    (define (static m)
      (cond ((eq? m 'new) (new))
            (else "random1: unknown static member" m)))
    ;
    (define (state data) (cadr data))
    ;
    (define (get-random-bytes data)
      (lambda (num) 
        (let ((draw (random (expt 2 (* 8 num)) (state data))))
          (integer->bytes draw num))))
    ;
    (define (get-seed)
      (let ((file (open-file "/dev/random" "rb")))
        (let ((bytes (read-bytes 32 file)))
          (close-port file)
          (bytes->integer bytes 32))))
    ;
    (define (new)
      (let ((seed (get-seed)))
        (let ((state (seed->random-state seed)))
          (this (list 'data state)))))
    ; returning static interface
    static))

         
