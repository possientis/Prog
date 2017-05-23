; both scm and guile

(newline)
(display "quasiquotes:\n")
(display (quasiquote (0 1 2)))(newline)                 ; (0,1,2)
(display `(0 1 2))(newline)
(newline)

(display "quasiquotes with unquote:\n")
(display (quasiquote (0 (unquote (+ 1 2)) 4)))(newline) ; (0,3,4) 
(display `(0 ,(+ 1 2) 4))(newline)                      ; (0,3,4) 
(display '(0 (unquote (+ 1 2)) 4))(newline)             ; (0 (unquote (+ 1 2)) 4)
(display '(0 ,(+ 1 2) 4))(newline)                      ; (0 (unquote (+ 1 2)) 4)
(newline)

(display "quasiquotes with unquote splicing:\n")
(display (quasiquote (0 (unquote-splicing (list 1 2)) 4)))(newline) ; (0 1 2 4)
(display `(0 ,@(list 1 2) 4))(newline)                              ; (0 1 2 4)

(display (quasiquote (0 (unquote (list 1 2)) 4)))(newline)          ; (0 (1 2) 4)
(display `(0 ,(list 1 2) 4))(newline)                               ; (0 (1 2) 4)


(exit 0)
