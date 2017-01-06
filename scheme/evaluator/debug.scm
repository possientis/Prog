;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-debug)) 
  (begin
    (define included-debug #f)
    (display "loading debug")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define __debug__ #t)

(define (set-debug flag)
  (cond ((eq? flag #t) (set! __debug__ #t))
        ((eq? flag #f) (set! __debug__ #f))
        (else (error "set-debug: invalid flag argument" flag))))

(set-debug #t) ; default

(define (get-debug) __debug__)

(define (debug message)
  (if __debug__ (display message)))

(define (debug-newline)
  (if __debug__ (newline)))

) (display "debug.scm is already loaded\n")) ; include guard

