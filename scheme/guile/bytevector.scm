(use-modules (rnrs bytevectors))

(define bv (make-bytevector 4))

(bytevector-u8-set! bv 0 #x12)
(bytevector-u8-set! bv 1 #x34)
(bytevector-u8-set! bv 2 #x56)
(bytevector-u8-set! bv 3 #x78)

(define out 
  (map (lambda (number)
         (number->string number 16))
       (list (bytevector-u8-ref bv 0)
             (bytevector-u16-ref bv 0 (endianness big))
             (bytevector-u32-ref bv 0 (endianness little)))))

(display out)(newline)  ; (12 1234 78563412)

; private key from mastering bitcoin
(define priv 
  #vu8(#x1e #x99 #x42 #x3a #x4e #xd2 #x76 #x08 
       #xa1 #x5a #x26 #x16 #xa2 #xb0 #xe9 #xe5
       #x2c #xed #x33 #x0a #xc5 #x30 #xed #xcc
       #x32 #xc8 #xff #xc6 #xa5 #x26 #xae #xdd))

(define number (bytevector-uint-ref priv 0 (endianness big) 32))

(display (number->string number 16))(newline)


 
