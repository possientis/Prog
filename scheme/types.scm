(define (type quoted-data)
  (cond ((boolean? quoted-data) 'boolean)
        ((symbol? quoted-data) 'symbol)
        ((char? quoted-data) 'char)
        ((vector? quoted-data) 'vector)
        ((procedure? quoted-data) 'procedure)
        ((pair? quoted-data) 'pair)
        ((number? quoted-data) 'number)
        ((string? quoted-data) 'string)
        ((null? quoted-data) 'empty-list)
        ;((port? quoted-data) 'port)
        (else 'unknown-type)))

