;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-object-string-primitive)) 
  (begin
    (define included-object-string-primitive #f)
    (display "loading object-string-primitive")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(require 'object->string)
(define (object->string-primitive object)
  (object->string object))

))  ; include guard
