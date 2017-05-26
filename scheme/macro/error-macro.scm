(require 'macro)

(define-syntax prohibit-one-arg
  (syntax-rules ()
    ((_ function argument) (if))  ; bogus expansion
    ((_ function . arguments) (function . arguments))))


(display (prohibit-one-arg + 2 3))(newline)

; error message is not helpful
;(prohibit-one-arg display 'foo)(newline)


(define-syntax syntax-error
  (syntax-rules ()
    ((syntax-error) (syntax-error "Bad use of syntax error!"))))

(define-syntax prohibit-one-arg2
  (syntax-rules ()
    ((_ function argument)
     (syntax-error "prohibit-one-arg2 cannot be used with one argument."
                   function
                   argument))
     ((_ function . arguments)(function . arguments))))

; error message is a lot better now
;(prohibit-one-arg2 display 'foo)


(exit 0)
