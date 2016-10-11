; Facade Design Pattern

; from GOF: provide a unified interface to a set of interfaces 
; in a subsystem. Facade defines a higher-level interface that 
; makes the subsystem easier to use.
;
; In this example (taken from GOF) , we present a compiler system 
; comprised of many complex elements: Scanner, ProgramNodeBuilder, 
; ProgramNode, Parser, RISCCodeGenerator.
;
; All these elements can be used by client code. However, in most
; cases client code simply wants to provide an input and retrieve
; the compiled output. We implement a 'Facade' for this system via
; the Compiler class and its 'compile' method.

; a type for source code inputs
(define input-stream  ; constructor
  (let ((let-for-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda(m)
        (cond ((eq? m 'filename) (filename data))
              (else (error "input-stream: unknown operation " m)))))
    ;
    (define (filename data) (cadr data))
    ;
    ; returning single argument constructor
    (lambda (filename) (this (list 'data filename)))))

; a type for compiled target code outputs
(define bytecode-stream  ; constructor
  (let ((let-for-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda(m)
        (cond (else (error "bytecode-stream: unknown operation " m)))))
    ;
    ; returning no argument constructor
    (lambda () (this (list 'data)))))

; a type for scanning: lexical analysis and token stream generation
(define scanner  ; constructor
  (let ((let-for-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda(m)
        (cond (else (error "scanner: unknown operation " m)))))
    ;
    ; returning single argument constructor
    (lambda (input) 
      (display "creating scanner from ")
      (display (input 'filename))(newline)
      (this (list 'data input)))))

; a builder type for abstract syntax tree
(define program-node-builder  ; constructor
  (let ((let-for-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda(m)
        (cond ((eq? m 'root-node) (tree data)) 
              (else (error "program-node-builder: unknown operation " m)))))
    ;
    (define (tree data) (cadr data))
    ;
    ; returning no argument constructor
    (lambda () 
      (display "creating builder for abstract syntax tree\n")
      (this (list 'data (program-node))))))

; a type for abstract syntax tree
(define program-node  ; constructor
  (let ((let-for-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda(m)
        (cond ((eq? m 'traverse) (traverse data)) 
              (else (error "program-node: unknown operation " m)))))
    ;
    (define (traverse data)
      (lambda (generator) ((generator 'visit) (self data))))
    ;
    (define (self data) (cadr data))
    ;
    ; returning no argument constructor
    (lambda () (let ((data (list 'data 'ref-to-self)))  ; setting up data
                 (let ((object (this data)))            ; creating object
                   (set-car! (cdr data) object)         ; updating object data
                   object)))))                          ; returning object

; a type for parsing tokens and building AST using builder
(define parser  ; constructor
  (let ((let-for-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda(m)
        (cond ((eq? m 'parse) (parse data)) 
              (else (error "parser: unknown operation " m)))))
    ;
    (define (parse data)
      (lambda (scanner-object builder)
        (display "parsing input and building syntax tree\n")))
    ;
    ; returning no argument constructor
    (lambda () 
      (display "creating new parser\n")
      (this (list 'data)))))

; a type for back end code generation
(define risc-code-generator  ; constructor
  (let ((let-for-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda(m)
        (cond ((eq? m 'visit) (visit data)) 
              (else (error "risc-code-generator: unknown operation " m)))))
    ;
    (define (visit data)
      (lambda (tree) (display "generating target code\n")))
    ;
    ; returning single argument constructor
    (lambda (output) 
      (display "creating target code generator\n")
      (this (list 'data output)))))

; now the Facade interface, stripping out the system complexity
; and allowing client to simply call the 'compile' method. 
(define compiler  ; constructor
  (let ((let-for-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda(m)
        (cond ((eq? m 'compile) (compile data)) 
              (else (error "compiler: unknown operation " m)))))
    ;
    (define (compile data)
      (lambda (input output)
        ; creating scanner from input-stream
        (let ((scanner-object (scanner input)))
        ; creating builder for abstract syntax tree
        (let ((builder (program-node-builder)))
        ; creating parser
        (let ((parser-object (parser)))
        ; parsing using scanner and builder, hence creating AST
        ((parser-object 'parse) scanner-object builder)
        ; creating target code generator
        (let ((generator (risc-code-generator output)))
        ; retrieving abstract syntax tree from builder
        (let ((parse-tree (builder 'root-node)))
        ; generating target code from AST and generator
        ((parse-tree 'traverse) generator)
        (display "compilation complete\n"))))))))
    ;
    ; returning no argument constructor
    (lambda () 
      (display "gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler\n")
      (this (list 'data)))))

; main
(define input   (input-stream "source.c"))
(define output  (bytecode-stream))
(define compiler-object (compiler))
((compiler-object 'compile) input output)
(exit 0)


