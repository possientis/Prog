(require 'macro)

(load "syntax-error.scm")

(define-syntax bind-variables
  (syntax-rules ()
    ((_ () form . forms) (begin form . forms))

    ((_ ((var val ooops . more) . more-bindings) form . forms)
     (syntax-error "bind-variables: illegal binding" (var val ooops . more)))

    ((_ ((var val) . more-bindings) form . forms)
     (let ((var val)) (bind-variables more-bindings form . forms)))

    ((_ ((var) . more-bindings) form . forms)
     (let ((var #f)) (bind-variables more-bindings form . forms)))

    ((_(var . more-bindings) form . forms) ; can't appear before
     (let ((var #f)) (bind-variables more-bindings form . forms)))

    ((_ bindings form . forms)
     (syntax-error "Bindings must be a list." bindings))))


(bind-variables () (display "hello ") (display "world!") (newline))

;ERROR: ... (#<id syntax-error:107fbe0> "bind-variables: illegal binding" (x 5 4))
; (bind-variables ((x 5 4)(y dont-care)) doesnt matter)

(bind-variables ((x 5)) (display "x = ")(display x)(newline))
(bind-variables ((x 5)(y 6)) (display "x + y = ")(display (+ x y))(newline))
(bind-variables ((x)) (display "x = ")(display x)(newline))
(bind-variables ((x)(y)) 
                (display "x = ")(display x)(display ", y = ")(display y)(newline))
(bind-variables (x) (display "x = ")(display x)(newline))
(bind-variables (x y) 
                (display "x = ")(display x)(display ", y = ")(display y)(newline))
(bind-variables (x (y 5)) 
                (display "x = ")(display x)(display ", y = ")(display y)(newline))

(bind-variables ((x 5)(y (* x 2))) (display "z = ") (display (+ x y)) (newline))

;ERROR: ... (#<id syntax-error:1c665f0> "Bindings must be a list." #f)
; (bind-variables #f (display "aint gona work!")(newline))




(exit 0)
    
