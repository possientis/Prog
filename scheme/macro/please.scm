(require 'macro)

(define-syntax please
  (syntax-rules ()
    ((please . forms) forms)))  ; returned form constructed by pattern matcher


(please display "foo\n")

; returned list constructed within the template of the macro
(define-syntax please2
  (syntax-rules ()
    ((please2 function . args) (function . args))))

(please2 display "bar\n")

(exit 0)
