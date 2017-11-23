(define call/cc call-with-current-continuation)

(define x (call/cc (lambda (k) (k 42))))
(define y (call/cc (lambda (k) (+ (k 42) 1729))))
(define z (let ((cont #f))
            (call/cc (lambda (k) (set! cont k)))
            (cont #f)))

(display x)(newline)    ; 42
(display y)(newline)    ; 42
(display z)(newline)    ; infinite loop

(exit 0)
