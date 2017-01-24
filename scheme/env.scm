(display (defined? extended-environment))(newline)  ; #f but why?? (see scm.pdf page 69)
(define env (extended-environment (a b c) (1 2 3) '()))
