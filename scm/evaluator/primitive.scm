;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-primitive)) 
  (begin
    (define included-primitive #f)
    (display "loading primitive")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; This file contains the list of primitive procedures which are defined in the
; global environment used by the interpreter. Most of these primitive procedures
; are directly defined in terms of a native scheme primitive, our 'car' body is 
; simply the native 'car', or 'cdr' the native 'cdr' etc.

; It may appear puzzling at first that not all primitives are defined with
; reference to a native scheme primitive. There are several reasons for this:

; Some primitives require arguments which are data structures specific to our
; implementation. For example the 'map' primitive requires a function object
; as argument and the native scheme function will not understand our own data
; representation. The 'object->string' primitive is another example. 

; Some primitives return values which are data structures specific to our 
; implementation. For example, the 'eval' primitive may return a function
; object after evaluating a lambda expression. 

; Some primitives have side-effects (i.e. they create changes to the global
; environment) and the interpreter's global environment is not the same as the 
; native scheme global environment. For example the 'eval' primitive may have 
; side effects due to 'set!', 'set-car!' and 'set-cdr!' or 'load' etc. Likewise, 
; the 'apply' primitive may have side-effects if executing a function with side 
; effects. The 'load' primitive executes code which is also likely to have side 
; effects. The 'require' primitive introduces new names in the global environment. 

; the 'display' primitive is an exception on this list as it did not need to
; be re-defined. We did so in order to distinguish native scheme's output from
; the interpreter's output. Hence we can see when native scheme is running,
; when interpreted code is running, or when code is interpreted by an interpreter
; whose code is itself interpreted...


(load "new-eval.scm")
(load "new-apply.scm")
(load "new-load.scm")
(load "new-require.scm")
(load "new-object-to-string.scm")
(load "new-map.scm")
(load "new-display.scm")

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'caar caar)
        (list 'caadr caadr)
        (list 'cdar cdar)
        (list 'cdadr cdadr)
        (list 'cadr cadr)
        (list 'caddr caddr)
        (list 'cadddr cadddr)
        (list 'cddr cddr)
        (list 'cdddr cdddr)
        (list 'cons cons)
        (list 'set-car! set-car!)
        (list 'set-cdr! set-cdr!)
        (list 'list list)
        (list 'append append)
        (list 'map new-map)
        (list 'null? null?)
        (list 'number? number?)
        (list 'string? string?)
        (list 'char? char?)
        (list 'boolean? boolean?)
        (list 'symbol? symbol?)
        (list 'pair? pair?)
        (list '+ +)
        (list '* *)
        (list '- -)
        (list '/ /)
        (list '= =)
        (list '< <)
        (list '> >)
        (list '<= <=)
        (list '>= >=)
        (list 'modulo modulo)
        (list 'equal? equal?)
        (list 'eq?    eq?)
        (list 'display new-display)
        (list 'newline newline)
        (list 'load    new-load)
        (list 'inexact->exact inexact->exact)
        (list 'number->string number->string)
        (list 'hash hash)
        (list 'require new-require)
        (list 'eval new-eval)
        (list 'apply new-apply)
        (list 'make-vector make-vector)
        (list 'vector-fill! vector-fill!)
        (list 'vector-length vector-length)
        (list 'vector-ref vector-ref)
        (list 'vector-set! vector-set!)
        (list 'string-append string-append)
        (list 'length length)
        (list 'object->string new-object->string)
        (list 'read read)
        (list 'open-file open-file)
        (list 'eof-object? eof-object?)
        (list 'close-port close-port)
        (list 'exit (lambda(x) 'ok))
        (list 'error error)
        ; more to be included
        ))
(define (primitive-procedure-names) (map car primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc) (make-primitive-procedure (cadr proc))) 
       primitive-procedures))

))  ; include guard 
