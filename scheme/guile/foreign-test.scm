(use-modules (bitcoin secp256k1))


(define %verify 257)
(define %sign 513)
(define %none 1)

(define p1 (context-create %verify)) 
(define p2 (context-create %sign)) 
(define p3 (context-create %none)) 

(display p1)(newline)
(display p2)(newline)
(display p2)(newline)


