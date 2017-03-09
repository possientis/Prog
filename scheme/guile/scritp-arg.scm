#!/usr/bin/guile \
-e main -s
!#
; see guile manual page 42 (62) about meta switch

(define (main args)
  (map (lambda (arg) (display arg) (display " "))
       (cdr args))
  (newline))
