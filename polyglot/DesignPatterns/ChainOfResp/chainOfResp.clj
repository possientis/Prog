; Chain of Responsibility Design Pattern
(ns chainOfResp (:gen-class)
  (:require [clojure.string :as string]))
; The Chain Of Responsibility design pattern is meant to decouple
; clients (which may have various requests) from request handlers
; which may be of different types. Rather than forcing a client
; to have the precise knowledge of which request handler is able
; to deal with which type of request, the Chain of Responsibility
; design pattern creates a common base interface to all request
; handlers, and unites them into a single linked list (a 'chain').
; Now the client only needs to know the head of the chain, to
; which it sends all of its requests. Each request handler, apart
; from maintaining a link to a 'successor', fundamentally has
; a 'handleRequest' method which now accepts all types of request.
; However, when faced with a request which it cannot fulfill, a 
; request handler will pass on the request to its successor. 
; Provided the chain of request handlers is properly set up, all
; requests should be handled appropriately.
;
; Note that this pattern can be generalized from 'chains' to non
; linear structure between objects, such as trees. One can imagine
; a network of request handlers, which are either dealing with 
; request themselves, or passing requests to other (linked) 
; request handlers
;
; This coding exercise is meant to provide a simulation of an ATM
; machine. As a server, the machine is able to provide a service
; 'getAmount' to an external client which consists in the delivery
; of the appropriate set of bank notes which corresponds to a 
; desired amount. As a client, the ATM machine relies on various
; request handlers, namely those which are specialized in the delivery
; of specific bank notes. So the machine relies on a service for the 
; delivery of $5 notes, another service for the delivery of $10 notes
; and so forth. This is a case where the Chain of Responsibility 
; design pattern can be successfully applied, allowing the implementation 
; of the ATM machine to forget about all those different services and 
; the details of how to convert an amount of cash into a set of notes.
;
;
; Our ATM machine only need to worry about the head of the chain of
; services, which it maintains as an internal data member. This machine
; has the ability to provide a set of bank notes from a desired amount
(declare RequestHandler)
(def ATMMachine   ; constructor
  (letfn
    [(getAmount [data]
       (fn [amount]
         (println "ATM machine: requesting amount if $" amount)
         (((:handler data) :handleRequest) amount))); delegating request to chain
     ; object created from data is message passing interface
     (this [data]
       (fn [m]
         (cond (= m :getAmount) (getAmount data)
               :else (throw (Exception. (format "ATM:unknown operation %s" m))))))]
    ;
    ; returning no argument constructor
    ;
    (fn [] (this { :handler (RequestHandler :getHandlingChain) }))))


; This is the base class, uniting all request handlers into a common
; interface. This class in normally abstract (the whole point of the
; design pattern is dealing with multiple types of request).

(declare RequestHandlerForFive 
         RequestHandlerForTen
         RequestHandlerForTwenty
         RequestHandlerForFifty)

(defmulti denomination :type)

(def RequestHandler ; constructor
  (letfn
    ;
    [(getHandlingChain []
       (RequestHandlerForFifty
         (RequestHandlerForTwenty
           (RequestHandlerForTen
             (RequestHandlerForFive nil)))))
     ;
     (handleRequest [data]
       (fn [amount]
         (let [denom ((:this data) :denomination)
               value (denom :value)]
           (cond (< amount 0) (throw (IllegalArgumentException.))
                 (= amount 0) '()
                 (not (= 0 (mod amount 5)))
                 (throw (Exception. "Requested amount should be multiple of $5"))
                 (>= amount value)
                 (cons denom ((handleRequest data) (- amount value)))
                 (not (nil? (:next data)))
                 (((:next data) :handleRequest) amount) ; passing on request
                 :else (throw (IllegalStateException. "chain badly set up"))))))
     ;
     ; object created from data is message passing interface
     ;
     (this [data]
       (fn [m]
         (cond (= m :handleRequest) (handleRequest data)
               (= m :denomination)  (denomination data)
               :else (throw (Exception. (format "RH: unknown operation %s" m))))))
     ;
     ; static interface
     ;
     (interface [& arg]
       (if (empty? arg) 
         (throw (Exception. "RH: argument missing"))
         ; else, at least one argument
         (if (empty? (rest arg))  ; single argument was passed
           (let [[m] arg]
             (cond (= m :getHandlingChain) (getHandlingChain) ; static call
             :else  (throw (Exception. (format "unknown static call &s" m)))))
           ; else, expecting two arguments, will return object instance 
           (let [[object-type object-next] arg
                 data {:type object-type :next object-next :this (ref nil)}
                 object (this data)]
             (dosync (ref-set (:this data) object))
             object))))]
     ;
     ; returning interface
     ;
    interface))

; default implementation
(defmethod denomination ::handle-request [data] 
  (throw (Exception. "HandleRequest::denomination is not implemented")))

; delivers $50 notes
(def Fifty  {:value 50})
(derive ::handle-request-for-fifty ::handle-request)
(defmethod denomination ::handle-request-for-fifty [data] Fifty)
(defn RequestHandlerForFifty [successor]
  (RequestHandler ::handle-request-for-fifty successor))


; delivers $20 notes
(def Twenty  {:value 20})
(derive ::handle-request-for-twenty ::handle-request)
(defmethod denomination ::handle-request-for-twenty [data] Twenty)
(defn RequestHandlerForTwenty [successor]
  (RequestHandler ::handle-request-for-twenty successor))


; delivers $10 notes
(def Ten  {:value 10})
(derive ::handle-request-for-ten ::handle-request)
(defmethod denomination ::handle-request-for-ten [data] Ten)
(defn RequestHandlerForTen [successor]
  (RequestHandler ::handle-request-for-ten successor))


; delivers $5 notes
(def Five  {:value 5})
(derive ::handle-request-for-five ::handle-request)
(defmethod denomination ::handle-request-for-five [data] Five)
(defn RequestHandlerForFive [successor]
  (RequestHandler ::handle-request-for-five successor))



(defn -main []
  (let [atm   (ATMMachine)
        nlist ((atm :getAmount) 235)
        vlist (map :value nlist)
        slist (map str vlist)]
    (println "The notes handed out by the ATM machine are:")
    (println (str "[" (string/join ", " (reverse slist)) "]"))))



