(require 'macro)

(define-syntax test-pattern
  (syntax-rules ()
    ((test-pattern) "match.0")
    ((test-pattern one) "match.1")
    ((test-pattern one two) "match.2")
    ((test-pattern one two three) "match.3")
    ((test-pattern . default) "fail")))


(display (test-pattern))(newline)                 ; match.0
(display (test-pattern 5))(newline)               ; match.1
(display (test-pattern 5 "abc"))(newline)         ; match.2
(display (test-pattern 5 "abc" #t))(newline)      ; match.3
(display (test-pattern 5 "abc" #t #\a))(newline)  ; match.4

(exit 0)



