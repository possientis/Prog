(define-module (bitcoin secp256k1)
  #:export 
    ( %context-verify
      %context-sign
      %context-none
      context-create
      context-clone
      context-destroy
      context-set-illegal-callback
    )
)

(use-modules (system foreign))

(define libsecp256k1 (dynamic-link "libsecp256k1"))


(define context-create
  (pointer->procedure 
    '* 
    (dynamic-func "secp256k1_context_create" libsecp256k1)
    (list int)))

(define context-clone
  (pointer->procedure
    '*
    (dynamic-func "secp256k1_context_clone" libsecp256k1)
    (list '*)))

(define context-destroy
  (pointer->procedure
    void
    (dynamic-func "secp256k1_context_destroy" libsecp256k1)
    (list '*)))

(define context-set-illegal-callback
  (pointer->procedure
    void
    (dynamic-func "secp256k1_context_set_illegal_callback" libsecp256k1)
    (list '* '* '*)))

(define %context-verify 257)
(define %context-sign 513)
(define %context-none 1)
