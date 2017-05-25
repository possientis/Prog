(require 'macro)

; dotted list allows implementation of variadic macros
(define-syntax when
  (syntax-rules ()
    ((when condition . body)  
     (if condition (begin . body) #f))))


(when #t 
  (display "This is true\n")
  (display "and this too")
  (newline))

(define-syntax when2
  (syntax-rules ()
    ((when2 condition form . forms)
     (if condition (begin form . forms) #f))))

(when2 #t 
  (display "This is still true\n")
  (display "and again this too")
  (newline))

(when #t) ; that'ok

; (when2 #t) ;ERROR: macro use does not match definition: (when2 #t)




(exit 0)

