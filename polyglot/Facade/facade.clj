; Facade Design Pattern
(ns facade (:gen-class))
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

(defmulti filename :type) 
; a type for source code inputs
(def InputStream  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :filename filename }]   
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               (throw (Exception. (format "InputStream: unknown operation %s" m)))
               (operation data))))))]
    ;
    ; returning single argument constructor
    ;
    (fn [file] (this {:type ::input-stream :file file})))) 

(defmethod filename ::input-stream [data] (:file data))

; a type for compiled target code outputs
(def BytecodeStream  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { }]  ; no method  
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               (throw 
                 (Exception. (format "BytecodeStream: unknown operation %s" m)))
               (operation data))))))]
    ;
    ; returning no argument constructor
    ;
    (fn [] (this {:type ::bytecode-stream})))) 

; a type for scanning: lexical analysis and token stream generation
(def Scanner  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { }]  ; no method  
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               (throw (Exception. (format "Scanner: unknown operation %s" m)))
               (operation data))))))]
    ;
    ; returning single argument constructor
    ;
    (fn [input] 
      (println "creating scanner from" (input :filename))
      (this {:type ::scanner :input input})))) 

(declare ProgramNode)
(defmulti root-node :type)
; a builder type for abstract syntax tree
(def ProgramNodeBuilder  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :root-node  root-node }]  
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               (throw 
                 (Exception. 
                   (format "ProgramNodeBuilder: unknown operation %s" m)))
               (operation data))))))]
    ;
    ; returning no argument constructor
    ;
    (fn [] 
      (println "creating builder for abstract syntax tree")
      (this {:type ::program-node-builder :tree (ProgramNode)})))) 

(defmethod root-node ::program-node-builder [data] (:tree data))

(defmulti traverse :type)
; a type for abstract syntax tree
(def ProgramNode  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :traverse  traverse }]  
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               (throw (Exception. (format "ProgramNode: unknown operation %s" m)))
               (operation data))))))]
    ;
    ; returning no argument constructor, object keeps a reference to itself
    ;
    (fn [] 
      (let [self (ref nil)
            object (this {:type ::program-node :self self })]
        (dosync (ref-set self object))
        object))))


(defmethod traverse ::program-node [data]
  (fn [generator] ((generator :visit) (:self data))))


(defmulti parse :type)
; a type for parsing tokens and building AST using builder
(def Parser  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :parse  parse }]  
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               (throw 
                 (Exception. 
                   (format "Parser: unknown operation %s" m)))
               (operation data))))))]
    ;
    ; returning no argument constructor
    ;
    (fn [] 
      (println "creating new parser")
      (this {:type ::parser})))) 

(defmethod parse ::parser [data]
  (fn [scanner builder]
    (println "parsing input and building syntax tree")))

(defmulti visit :type)
; a type for back end code generation
(def RISCCodeGenerator  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :visit  visit }]  
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               (throw 
                 (Exception. 
                   (format "RISCCodeGenerator: unknown operation %s" m)))
               (operation data))))))]
    ;
    ; returning single argument constructor
    ;
    (fn [output] 
      (println "creating target code generator")
      (this {:type ::risc-code-generator :output output})))) 

(defmethod visit ::risc-code-generator [data]
  (fn [tree] (println "generating target code")))

(defmulti compile-action :type)
; now the Facade interface, stripping out the system complexity
; and allowing client to simply call the 'compile' method. 
(def CompilerClass  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [class-dictionary { :compile  compile-action }]  
         (fn [m]
           (let [operation  (class-dictionary m :notfound)]
             (if (= operation :notfound)
               (throw 
                 (Exception. 
                   (format "CompilerClass: unknown operation %s" m)))
               (operation data))))))]
    ;
    ; returning no argument constructor
    ;
    (fn [] 
      (println "gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler")
      (this {:type ::compiler}))))

(defmethod compile-action ::compiler [data]
  (fn [input output]
    (let 
      ; creating scanner from InputStream 
      [ scanner (Scanner input)
      ; creting builder for abstract syntax tree
        builder (ProgramNodeBuilder)
      ; creating parser
        parser  (Parser)]
      ; parsing using scanner and builder, hence creating AST
      ((parser :parse) scanner builder)
      (let
        ; creating target code generator
        [ generator (RISCCodeGenerator output)
        ; retrieving abstract syntax tree from builder
          parse-tree (builder :root-node)]
        ; generating target code from AST and generator
        ((parse-tree :traverse) generator)
        (println "compilation complete")))))

(defn -main []
(def input  (InputStream "source.c"))
(def output (BytecodeStream))
(def compiler (CompilerClass))
((compiler :compile) input output))





