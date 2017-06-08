(use-modules (bitcoin secp256k1))

(define p1 (context-create %context-verify)) 
(define p2 (context-create %context-sign)) 
(define p3 (context-create %context-none)) 

(display p1)(newline)
(display p2)(newline)
(display p2)(newline)


