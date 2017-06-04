(define x (dynamic-link "libsecp256k1"))


(display "x = ")(display x)(newline)    ; x = #<dynamic-object libsecp256k1>
(display (dynamic-object? x))(newline)  ; #t

(define context-create (dynamic-func "secp256k1_context_create" x))




(dynamic-unlink x)
(display "x = ")(display x)(newline); x = #<dynamic-object libsecp256k1 (unlinked)>
(display (dynamic-object? x))(newline)  ; #t

(exit 0)
