#|
; this code will fail
(define x 
  (let ((loop 
          (lambda (n)
            (if (= 0 n)
              1
              (* n (loop (- n 1)))))))
    (loop 5)))
|#

; ((lambda (loop) (loop 5)) (lambda (n) (if (= 0 n) 1 (* n (loop (- n 1)))))),  Env = {} (i.e. just primitives)
; proc1 = (lambda (loop) (loop 5))                          , Env = {}
; proc2 = (lambda (n) (if (= 0 n) 1 (* n (loop (- n 1)))))  , Env = {} --> this is the key: static scoping, the procedure object created has Env = {}
; we apply proc1 to proc2: the body of proc1 is evaluated in *** proc1 environment **** extended with 'loop' is bound to proc2
; (loop 5)                                                  , Env = { loop : proc2 }
; we apply proc2 to 5: the body of proc2 is evaluated in **** proc2 environment ***** extended with 'n' bound to 5
; (if (= 0 n) 1 (* n (loop (- n 1))))                       , Env = {n:5}  --> this environement has no binding for 'loop', hence failure

; conclusion : Failure occurs because (lambda (n) (if (= 0 n)) 1 (* n (loop (- n 1)))) is evaluated in an environment which has no binding for 'loop'.
; so although such evaluation is succesful, due to static scoping, the procedure object created from the evaluation contains an environment without
; binding for 'loop'. Hence when this procedure is applied to '5', it needs to evaluate its body in an environment without binding for 'loop'.

; TODO : understand why this code is succesful

(define x
  (begin
    (define (loop n)
      (if (= 0 n) 1 (* n (loop (- n 1)))))
    (loop 5)))

















    


