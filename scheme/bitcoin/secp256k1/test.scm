(use-modules (bitcoin secp256k1))

(define ctx1 (context-create %context-verify)) 
(define ctx2 (context-create %context-sign)) 
(define ctx3 (context-create %context-none)) 
(define ctx4 (context-clone ctx1))


(display ctx1)(newline)
(display ctx2)(newline)
(display ctx3)(newline)
(display ctx4)(newline)

(context-destroy ctx1)
(context-destroy ctx2)
(context-destroy ctx3)
(context-destroy ctx4)


