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
       (let [class-dictionary { :traverse  traverse 
                                :self :self}]  
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


(def x (ProgramNode))
(def y (x :self))
(println (= x y))






