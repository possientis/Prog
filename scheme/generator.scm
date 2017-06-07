(define generate
  (let ((state 0))
    (lambda ()
      (let ((read-state state))
        (set! state (+ state 1))
        read-state))))

(display (generate))(newline)
(display (generate))(newline)
(display (generate))(newline)
(display (generate))(newline)
(display (generate))(newline)

(define (make-generator init-value proc)
  (let ((state init-value))
    (lambda ()
      (let ((read-state state))
        (set! state (proc state))
        read-state))))

(define gen1 (make-generator 5 (lambda (x) (+ x 3))))

(newline)
(display (gen1))(newline)
(display (gen1))(newline)
(display (gen1))(newline)
(display (gen1))(newline)


(exit 0)
