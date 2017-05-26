(require 'macro)

(load "syntax-error.scm")

(define-syntax bind-variables
  (syntax-rules ()
    ((_ () form . forms) (begin form . forms))

    ((_ ((var val ooops . more) . more-bindings) form . forms)
     (syntax-error "bind-variables: illegal binding" (var val ooops . more)))

))


(bind-variables () (display "hello ") (display "world!") (newline))

;ERROR: ... (#<id syntax-error:107fbe0> "bind-variables: illegal binding" (x 5 4))
; (bind-variables ((x 5 4)(y dont-care)) doesnt matter)



(exit 0)
    
