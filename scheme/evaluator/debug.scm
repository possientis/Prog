;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-debug)) 
  (begin
    (define included-debug #f)
    (display "loading debug")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define __debug__ #t)
(define __debug-level__ #f)

(define (set-debug flag)
  (cond ((eq? flag #t) (set! __debug__ #t))
        ((eq? flag #f) (set! __debug__ #f))
        (else (error "set-debug: invalid flag argument" flag))))

(define (set-debug-level lvl) (set! __debug-level__ lvl))

(set-debug #t)        ; default
(set-debug-level #f)  ; default

(define (get-debug) __debug__)
(define (get-debug-level) __debug-level__)

(define (debug message)
  (if (eq? #f (get-debug-level))  ; don't care about interpreter's level
    (if __debug__ (display message)))
    (if (and __debug__ (eq? (get-debug-level) (scheme-interpreter-level)))
      (display message)))

(define (debug-newline)
  (if (eq? #f (get-debug-level))  ; don't care about interpreter's level
    (if __debug__ (newline)))
    (if (and __debug__ (eq? (get-debug-level) (scheme-interpreter-level)))
      (newline)))


)) ; include guard

