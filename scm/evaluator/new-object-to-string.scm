;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-object-to-string)) 
  (begin
    (define included-new-object-to-string #f)
    (display "loading new-object-to-string")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(require 'object->string)
(define (new-object->string object)
  (object->string object))

))  ; include guard
