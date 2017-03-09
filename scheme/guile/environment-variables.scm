; controlled by GUILE_LOAD_COMPILED_PATH

(define (print x) (display x)(newline))

(newline)
(display "GUILE_LOAD_COMPILED_PATH:")(newline)
(for-each print %load-compiled-path)

(newline)
(display "GUILE_LOAD_PATH:")(newline)
(for-each print %load-path)


