(require 'macro)

(define-syntax my-macro
  (syntax-rules ()
    ((_ a b c)
     (begin
      (display "debugging template for my-macro:\n")
      (display "a is ")(display a)(newline)
      (display "b is ")(display b)(newline)
      (display "c is ")(display c)(newline)))))


(my-macro 12 '(1 2 3) "abc")

(exit 0)
