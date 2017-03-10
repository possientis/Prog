#!/usr/bin/guile \
-e entry-func -s
!#

; try ./command-line.scm a b c

; this is running first
(display "first: ")(display (command-line))(newline)       ; guile only, same as 'program-arguments'
(display "second: ")(display (program-arguments))(newline)  ; scm and guile


; then entry point
(define (entry-func args)
  (display "third")(display args)(newline))


