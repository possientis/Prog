(require 'macro)

(define-syntax syntax-error
  (syntax-rules ()
    ((_) (syntax-error "Bad usage of syntax-error"))))

;ERROR: ... : (#<id syntax-error:1aa5980> "Bad usage of syntax-error")
;(syntax-error)


(define-syntax my-named-let
  (syntax-rules ()
    ((_ () . ignore) (syntax-error "NAME must not be the empty list."))
    ((_ (car . cdr) . ignore) (syntax-error "NAME must be symbol." (car . cdr)))
    ((_ name bindings form . forms)
     (let name bindings form . forms))))

(define fact5
(my-named-let 
  loop ((x 5) (acc 1))
  (if (= 0 x)
    acc
    (loop (- x 1) (* x acc)))))

(display fact5)(newline)





(exit 0)


