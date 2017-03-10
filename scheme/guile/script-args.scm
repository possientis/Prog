#!/usr/bin/guile \
-e main -s
!#
; see guile manual page 42 (62) about meta switch
; with the -e main, guile will call 'main' with 
; the (command-line) as its arguments.

(define (main args)
  (display args) (newline))


; However, code outside of main will be executed first
(display "I am running before main\n")
