(define-module (foo bar-module)
               #:export (frob))

(define (frob x)
  (display "\nfrob function of module 'foo/bar-module' is running ...\n")
  (* 2 x))
