(use-modules 
  (bitcoin foreign)
  (system foreign))

;;; names defined in (system foreign)
;;; these names can be used to describe C types in FFI
;;; The symbol '* can be used to refer to pointer types.
(display void)(newline)     ; 0
(display float)(newline)    ; 1
(display double)(newline)   ; 2
(display uint8)(newline)    ; 3
(display int8)(newline)     ; 4
(display uint16)(newline)   ; 5
(display int16)(newline)    ; 6
(display uint32)(newline)   ; 7
(display int32)(newline)    ; 8
(display uint64)(newline)   ; 9
(display int64)(newline)    ; 10

;;; platform specific
(display (eq? int int32))(newline)            ; #t for x86-64
(display (eq? unsigned-int uint32))(newline)  ; #t for x86-64
(display (eq? long int64))(newline)           ; #t for x86-64
(display (eq? unsigned-long uint64))(newline) ; #t for x86-64
(display (eq? size_t uint64))(newline)        ; #t for x86-64
(display (eq? ssize_t int64))(newline)        ; #t for x86-64
(display (eq? ptrdiff_t int64))(newline)      ; #t for x86-64


(display %foreign-int-ptr)(newline)




