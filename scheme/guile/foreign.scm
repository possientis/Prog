(use-modules (system foreign))


(display int8)(newline)   ; 4
(display uint8)(newline)  ; 4
(display uint16)(newline) ; 5
(display double)(newline) ; 2
(display int)(newline)    ; 8
(display unsigned-int)(newline) ; 7
(display long)(newline)   ; 10
(display size_t)(newline) ; 9
(display void)(newline)   ; 0

(define mylib (dynamic-link "libsecp256k1"))

(define ptr (dynamic-pointer "secp256k1_context_create" mylib))

(display "ptr = ")(display ptr)(newline)

