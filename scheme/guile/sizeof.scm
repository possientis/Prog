(use-modules (system foreign))

(define ptr (make-c-struct `(,int ,int) '(300 43)))

(display ptr)(newline)
