#!/usr/bin/guile -s
!#

(define (fact n)
  (if (zero? n) 1
    (* n (fact (- n 1)))))

; problem is that we cannot reuse the definition of 'fact'
; simply by loading this file, see 'fact2.scm'
; guile -l fact1.scm will fail

(display (fact (string->number (cadr (command-line)))))
(newline)
