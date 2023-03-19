(define-module (math bessel)
               #:export (j0))
; you can load shared library using full path
;(load-extension "./libguile-bessel.so" "init_bessel")

; or simply using library name. However, guile must be
; able to locate the shared library libguile-bessel.so
; create a symlink into /usr/lib/x86_64-linux-gnu/guile/2.2/extensions
; create directory

(load-extension "libguile-bessel" "init_bessel")

