;; This works with mit-scheme but fails with scm
(define-syntax push
  (syntax-rules ()
                ((push item list)
                 (set! list (cons item list)))))
