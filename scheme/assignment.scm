;; simple function with state such that
;; (f 0) followed by (f 1) produces a
;; different result from (f 1) followed by (f 0)
;; this allows us to determine the order of
;; evaluation of arguments in procedure calls
;; by evaluating (+ (f 0) (f 1))

(define f
  (let ((init-flag #f))
    (lambda (x)
      (if init-flag
        x
        (begin (set! init-flag  #t) 0))))) ; returns 0 on first call regardless

(define (which-scheme)
  (let ((f
    (let ((init-flag #f))
      (lambda (x)
        (if init-flag
          x
          (begin (set! init-flag  #t) 0))))))
    (if (= (+ (f 0) (f 1)) 0)
      'mit-scheme   ; evaluation from right to left
      'scm)))       ; evaluation from left to right


