;something is missing
(require 'clojure.java.io)
(defn reply-type [reply]
  :TBI)


(defmulti parse-reply reply-type :default :unknown)
(defmethod parse-reply :unknown
  [#^BufferedReader reader]
  (throw (Exception. (str "Unknown reply type:"))))
(defmethod parse-reply \-
  [#^BufferedReader reader]
  (let [error (read-line-crlf reader)]
    (throw (Exception. (str "Server error: " error)))))
(defmethod parse-reply \+
  [#^BufferedReader reader]
  (read-line-crlf reader))
(defmethod parse-reply \$
  [#^BufferedReader reader]
  (let [line (read-line-crlf reader)
        length (parse-int line)]
    (if (< length 0)
      nil
      (let [#^chars cbuf (char-array length)]
        (do
            (do-read reader cbuf 0 length)
          (read-crlf reader) ;; CRLF
          (String. cbuf))))))
(defmethod parse-reply \*
  [#^BufferedReader reader]
  (let [line (read-line-crlf reader)
        count (parse-int line)]
    (if (< count 0)
      nil
      (loop [i count
             replies []]
        (if (zero? i)
          replies
          (recur (dec i) (conj replies (read-reply reader))))))))
(defmethod parse-reply \:
  [#^BufferedReader reader]
  (let [line (trim (read-line-crlf reader))
        int (parse-int line)]
    int))
