(load "main.scm")                 ; setting up interpreter

(strict-eval '(load "lazy.scm"))  ; defining 'lazy?'

(display (strict-eval '(lazy?)))(newline)
(display (strict-eval '(lazy?)))(newline)
(display (analyze-eval '(lazy?)))(newline)
(display (force-thunk (lazy-eval '(lazy?))))(newline)
(display (analyze-eval '(lazy?)))(newline)
(display (force-thunk (lazy-eval '(lazy?))))(newline)
(display (strict-eval '(lazy?)))(newline)
(display (force-thunk (lazy-eval '(lazy?))))(newline)


(exit 0)
