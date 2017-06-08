(define-module (bitcoin secp256k1)
  #:export 
    ( context-create 
      %context-verify
      %context-sign
      %context-none
    )
)

(use-modules (system foreign))

(define libsecp256k1 (dynamic-link "libsecp256k1"))


(define context-create
  (pointer->procedure 
    '* 
    (dynamic-func "secp256k1_context_create" libsecp256k1)
    (list int)))

(define %context-verify 257)
(define %context-sign 513)
(define %context-none 1)
