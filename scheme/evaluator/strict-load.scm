;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-strict-load)) 
  (begin
    (define included-strict-load #f)  ; include guard
    (display "loading strict-load")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The strict-load function is fundamentally a strict-eval function.
; The only difference lies in the argument referring to the expression
; being evaluated. In the case of strict-load, the expression being 
; evaluated is simply the code contained within the filename argument.
;
; However, contrary to strict-eval which has an optional environment 
; argument, we have chosen not to include such argument for strict-load.
;
; We shall now attempt to explain this choice: When making a call to
; strict-load in relation to <filename> in an environment <env>:
;
; (strict-load <filename> <env>)
;
; The likelihood is <filename> will itself import other file 
; dependencies via the 'load' function:
;
; details of <filename>:
;
; ...
; (load <file1>)
; (load <file2>)
; ...
;
; However, the 'load' function in scheme (just like 'eval') does not allow
; you to specifiy an environment argument. Hence, when calling strict-load
; on <filename> and <env> we are instructing the evaluator to evaluate the
; expression '(load <file1>)' in the environment <env>, but this environment
; has no impact on the evaluation, as the evaluation of '(load <file1>)' 
; calls for the evaluation of <file1> in the default environment global-env.
; Another way to look at the problem is to compare the calls to:
;
; (strict-load <filename> <env>)
;
; (strict-load <filename'> <env>)
;
; where <filename'> is simply the code '(load <filename>)'. We would like 
; these two calls to have identical semantics and yet they would not, as the 
; first call would attempt to evaluate <filename> in the environment <env> 
; (but cannot be successful as it would pick the wrong environment to evaluate 
; any 'load' statement within <filename>), while the second would evaluate 
; <filename> in the environment global-env.
;
; Conclusion: Allowing an <env> argument for strict-load would mislead the
; user into expecting a particular semantics which cannot be implemented
;
; At this point, one question naturally arises: why do we allow strict-eval
; to have an <env> argument?. After all, the scheme function 'eval' (just
; like 'load') does not have an <env> argument, and calling:
;
; (strict-eval <exp> <env>)
;
; on an expression <exp> containing an 'eval' statement will likewise evaluate 
; the argument of 'eval' in the environment global-env (rather than <env>).
;  
; So why? The answer is we cannot do without it: in order to implement the 
; semantics of a function call '(f a b c d)' we need to evaluate the body of
; the function 'f' in a specific environment which is not global-env.
;
; Of course, this means that if the body of the function 'f' contains an 'eval'
; statement, the expression argument of such 'eval' statement will be evaluated
; in the 'wrong' environment global-env.
;
; (define x 20)
; (define (f x) (display "x = ") (display (eval 'x)) (newline))
; (f 5) ; x = 20
;
;  
(define (strict-load filename)
  (let ((env global-env) (code (filename->code filename)))
    (strict-eval code env)
    unspecified-value))

))  ; include guard
