;(require 'macro)   ; for scm 

(define-syntax let*
  (syntax-rules ()
    ((_ () b1 b2 ...) (let () (display "let* base case:\n") b1 b2 ...))
    ((_ ((i1 e1) (i2 e2) ...) b1 b2 ...)
     (let ((i1 e1))
       (display "let* main case:\n")
       (let* ((i2 e2) ...) b1 b2 ...)))))


(display (let* ((x 5)(y (+ 2 x))) (* x y)))(newline)




(exit 0)


