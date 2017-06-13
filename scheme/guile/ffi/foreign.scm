(define-module (bitcoin foreign)
  #:export
    ( %foreign-int-ptr
    )
)

(use-modules (system foreign))

(define libforeign (dynamic-link "libforeign"))

(define %foreign-int-ptr (dynamic-pointer "foreign_int" libforeign))

