(display (defined? 'foo))(newline)  ; would be unquoted in scm

(define foo 5)

(display (defined? 'foo))(newline)  ; would be unquoted in scm

(exit 0)
