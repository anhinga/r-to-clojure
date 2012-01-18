(ns RClj.utils

  "General utility functions and macros.  Basically these resources are
   fairly general and intended to be usable on most any project"

  (:require [clojure.contrib.math :as math]
            [clojure.contrib.string :as str]
            [clojure.contrib.str-utils :as stru]
            [clojure.set :as set]
            [clojure.contrib.seq :as seq]
            [clojure.zip :as zip]
            [clojure.contrib.io :as io]
            [clojure.contrib.properties :as prop]
            [clojure.xml :as xml]
            [RClj.fs :as fs]
	    )

  (:use [clojure.contrib.condition
         :only [raise handler-case *condition*
                print-stack-trace stack-trace-info]]
        [clojure.java.shell
         :only (sh)]
        [clojure.contrib.pprint
         :only (cl-format compile-format)])

  (:import (java.util Date Calendar Locale)
           java.lang.Thread
           (java.text SimpleDateFormat)))



;;; (compile 'edu.bc.utils)


(defn div [l r]
  (let [q (math/floor (/ l r))]
    [q (rem l r)]))


(defn primes
  "RHickey paste.lisp.org with some fixes by jsa. Returns a list of
   all primes from 2 to n.  Wicked fast!" [n]
  (if (< n 2)
    ()
    (let [n (int n)]
      (let [root (int (Math/round (Math/floor (Math/sqrt n))))]
        (loop [i (int 3)
               a (int-array (inc n))
               result (list 2)]
          (if (> i n)
            (reverse result)
            (recur (+ i (int 2))
                   (if (<= i root)
                     (loop [arr a
                            inc (+ i i)
                            j (* i i)]
                       (if (> j n)
                         arr
                         (recur (do (aset arr j (int 1)) arr)
                                inc
                                (+ j inc))))
                     a)
                   (if (zero? (aget a i))
                     (conj result i)
                     result))))))))


(defn prime-factors [num]
  (loop [ps (primes (int (math/sqrt num)))
         factors []]
    (if (empty? ps)
      factors
      (let [pf (loop [n num
                      cnt 0]
                 (let [f (first ps)
                       [q r] (div n f)]
                   (if (not= 0 r)
                     (when (> cnt 0) [f cnt])
                     (recur q (inc cnt)))))]
        (recur (rest ps)
               (if pf (conj factors pf) factors))))))



(defn merge-with*
  "Merge-with needs to call user supplied F with the KEY as well!!!
  Returns a map that consists of the rest of the maps conj-ed onto the
  first.  If a key occurs in more than one map, the mapping(s) from
  the latter (left-to-right) will be combined with the mapping in the
  result by calling (f key val-in-result val-in-latter)."
  {:added "1.jsa"} [f & maps]
  (when (some identity maps)
    (let [merge-entry (fn [m e]
                        (let [k (key e) v (val e)]
                          (if (contains? m k)
                            (assoc m k (f k (get m k) v))
                            (assoc m k v))))
          merge2 (fn [m1 m2]
                   (reduce merge-entry (or m1 {}) (seq m2)))]
      (reduce merge2 maps))))


(defn ensure-vec [x]
  (cond
   (vector? x) x
   (seq? x) (vec x)
   (map? x) (vec x)
   true [x]))


(defn in [e coll]
  (if (map? coll)
    (find coll e)
    (some #(= % e) coll)))


(defn pos
  "Returns a lazy seq of positions of X within COLL taken as a sequence"
  [x coll]
  (keep-indexed #(when (= x %2) %1) coll))

(defn pos-any
  "Returns a lazy seq of positions of any element of TEST-COLL within
   COLL taken as a sequence"
  [test-coll coll]
  (keep-indexed #(when (in %2 test-coll) %1) coll))


(defn random-subset [s cnt]
  (let [s (seq (set s))]
    (cond
     (<= cnt 0) #{}
     (<= (count s) cnt) (set s)
     :else
     (loop [ss #{(rand-nth s)}]
       (if (= (count ss) cnt)
         ss
         (recur (conj ss (rand-nth s))))))))


(defn drop-until [pred coll] (drop-while (complement pred) coll))
(defn take-until [pred coll] (take-while (complement pred) coll))




(def ^{:private true} *uid* (atom (.getTime (Date.))))

(defn gen-uid []
  (swap! *uid* inc))

(defn gen-kwuid []
  (keyword (str (gen-uid))))



(defn sleep [msecs]
  (Thread/sleep msecs))

(defn str-date
  ([] (str-date (Date.) "yyyy-MM-dd HH:mm:ss"))
  ([fm] (str-date (Date.) fm))
  ([d fm] (.format (SimpleDateFormat. fm) d)))




;;; -----------------------------------------------------------------
;;; Various ancillary string stuff.  Again, eventually these pieces
;;; should be refactored into utils.* name spaces and files

;;; These are a bit duff.  Something like this should really be in
;;; clojure.string, clojure.contrib.string or clojure.str-utils
;;;
(defn string-less?
  [l r]
  "Case insensitve string comparison.  Usable as a sort comparator"
  (neg? (.compareToIgnoreCase l r)))

(defn string-greater?
  [l r]
  "Case insensitve string comparison.  Usable as a sort comparator"
  (pos? (.compareToIgnoreCase l r)))

(defn string-equal?
  [l r]
  "Case insensitve string comparison.  Usable as a sort comparator"
  (zero? (.compareToIgnoreCase l r)))



(defn intstg?
  "Test and return whether S is a string of only digits 0-9.  If so,
  return generalized boolean else return nil/false"
  [s]
  (let [hit (re-find #"[0-9]+" s)]
    (and hit (= hit s))))




;;; Fixed cost Edit distance.
;;;
;;; (levenshtein "this" "")
;;; (assert (= 0 (levenshtein "" "")))
;;; (assert (= 3 (levenshtein "foo" "foobar")))
;;; (assert (= 3 (levenshtein "kitten" "sitting")))
;;; (assert (= 3 (levenshtein "Saturday" "Sunday")))
;;; (assert (= 22 (levenshtein
;;;   "TATATTTGGAGTTATACTATGTCTCTAAGCACTGAAGCAAA"
;;;   "TATATATTTTGGAGATGCACAT"))
;;;
(defn- new-row [prev-row row-elem t]
  (reduce
   (fn [row [d-1 d e]]
     (conj row (if (= row-elem e) d-1 (inc (min (peek row) d d-1)))))
    [(inc (first prev-row))]
    (map vector prev-row (next prev-row) t)))

(defn levenshtein [s t]
  (cond
   (= s t "") 0
   (= 0 (count s)) (count t)
   (= 0 (count t)) (count s)
   :else
   (peek (reduce
          (fn [prev-row s-elem] (new-row prev-row s-elem t))
          (range (inc (count t)))
          s))))


;;; Simple ngram comparison.  Metric is
(defn letter-pairs [s n]
  (set (map #(apply str %) (partition n 1 s))))

(defn word-letter-pairs [s n]
  (reduce (fn[m s] (set/union m (letter-pairs s n))) #{} (str/split #" " s)))

(defn ngram-compare [s1 s2 & {uc? :uc? n :n :or {n 2 uc? true}}]
  (let [wlp1 (word-letter-pairs (if uc? (str/upper-case s1) s1) n)
        wlp2 (word-letter-pairs (if uc? (str/upper-case s2) s2) n)]
    (/ (* 2 (count (set/intersection wlp1 wlp2)))
       (+ (count wlp1) (count wlp2)))))

;;;(float (ngram-compare "FRANCE" "french"))
;;;(float (ngram-compare "FRANCE" "REPUBLIC OF FRANCE"))
;;;(float (ngram-compare "FRENCH REPUBLIC" "republic of france"))
;;;(float (ngram-compare
;;;        "TATATTTGGAGTTATACTATGTCTCTAAGCACTGAAGCAAA"
;;;        "TATATATTTTGGAGATGCACAT"))




;;; -----------------------------------------------------------------
;;; Simple vector stuff.  dot product, norm, distances, and such.


(defn dot [v1 v2]
  (reduce #(+ %1 %2) 0 (map #(* %1 %2) v1 v2)))

(defn norm [v]
  (math/sqrt (dot v v)))

(defn vhat [v]
  (let [n (norm v)] (vec (map #(/ % n) v))))

(defn cos-vangle [v1 v2]
  (dot (vhat v1) (vhat v2)))

(defn vangle-dist [v1 v2]
  (math/abs (dec (cos-vangle v1 v2))))

(defn vecdist [v1 v2]
  (let [v (vec (map #(- %1 %2) v1 v2))] (dot v v)))


(defn normed-codepoints [s]
  (vec (map #(let [nc (- % 97)]
               (cond
                (>= nc 0) nc
                (= % 32) 27
                :else 28))
            (str/codepoints s))))

(defn ngram-vec [s & {n :n :or {n 2}}]
  (let [ngrams (word-letter-pairs s n)
        ngram-points (map (fn [[x y]]
                            (int (+ (* x 27) y)))
                          (map normed-codepoints ngrams))
        v (int-array 784 0)]
    (doseq [i ngram-points]
      (aset v i 1))
    v))




;;; ----------------------------------------------------------------
;;; Slightly abstracted things from Java that are often used from/in
;;; many contexts...

(defn sys-property [prop-name]
  "Return the System property with name PROP-NAME (a string)"
  (System/getProperty prop-name))

(defn sys-properties []
  "Return the set of System properties as a map"
  (System/getProperties))

(defn classpath []
  (str/split #":" (sys-property "java.class.path")))

(defn getenv [ev]
  "Return the value of the environment variable EV (a string)"
  (System/getenv ev))




;;; ----------------------------------------------------------------
;;; Some simple text file processing utils.


(defn reduce-file [fname func acc]
  "Reduce text file denoted by FNAME (filespec/File obj) using function
   FUNC per line and reduction seed accumulator ACC.  FUNC is a function
   of two arguments: first is the current line from file and second is
   the current value of ACC"
  (reduce func acc (io/read-lines (io/file-str fname))))


(defn process-line [acc line]
  (reduce #(assoc %1 %2 (inc (get %1 %2 0))) acc (str/split #"," line)))


(defmacro do-text-file [[in & options] & body]
  `(doseq [~'$line (io/read-lines (io/file-str ~in))]
     (do ~@body)))


(defmacro do-text-to-text [[in out] & body]
  `(io/with-out-writer (io/file-str ~out)
     (doseq [~'$line (io/read-lines (io/file-str ~in))]
       (let [result# (do ~@body)]
         (when result#
           (println result#))))))




;;; ----------------------------------------------------------------
;;; Definition macros and helpers for providing proper keyword
;;; arguments and maintaining doc string, user meta data, and special
;;; pre and post condition meta data.  Actually, this is just curried
;;; into the pre and post processing of the body.  This should really
;;; be resubmitted to clojure.contrib.def as the defnk and helper
;;; there do not account for pre and post conditions.


(defn name-with-attrs [name macro-args]
  "To be used in macro definitions.
   Handles optional docstrings and attribute maps for a name to be defined
   in a list of macro arguments. Also handles pre/post conditions. If the
   first macro argument is a string, it is added as a docstring to name and
   removed from the macro argument list. If afterwards the first macro argument
   is a map, its entries are added to the name's metadata map and the map is
   removed from the macro argument list. If the first form past the arg list
   is a map with :pre and/or :post, the map is removed and the pre and post
   vectors of forms are separated out.  The return value is a vector containing
   the name with its extended metadata map, the args form, followed by the pre
   and post forms (if any) and lastly, the body forms."
  [name macro-args]
  (let [[docstring macro-args] (if (string? (first macro-args))
                                 [(first macro-args) (next macro-args)]
                                 [nil macro-args])
        [attr macro-args]      (if (map? (first macro-args))
                                 [(first macro-args) (next macro-args)]
                                 [{} macro-args])
        attr                   (if docstring
                                 (assoc attr :doc docstring)
                                 attr)
        attr                   (if (meta name)
                                 (conj (meta name) attr)
                                 attr)
        [pre-post args body]   (if (and (map? (second macro-args))
                                        (or ((second macro-args) :pre)
                                            ((second macro-args) :post)))
                                 [(second macro-args)
                                  (first macro-args)
                                  (drop 2 macro-args)]
                                 [nil (first macro-args) (drop 1 macro-args)])
        [pre post]             (if pre-post
                                 [(pre-post :pre) (pre-post :post)]
                                 [nil nil])]
    [(with-meta name attr) args pre post body]))


(defmacro defnk [name & args-body]
  "Same as DEFN, but supports keyword style arguments.  Adapted and modified
   from Rich Hickey's original on google groups Clojure group, to support doc
   strings, meta data, and pre/post conditions."
  (let [[sym args pre post body] (name-with-attrs name args-body)
        pos-keys (split-with (complement keyword?) args)
        ps (pos-keys 0)
        ks (apply array-map (pos-keys 1))
        gkeys (gensym "gkeys__")
        letk (fn [ke]
               (let [k (key ke)
                     ;; The next oddity is due to some weird bug in
                     ;; Clojure 1.2 - for some reason in this context
                     ;; name returns nil despite k being a keyword!??!
                     kname (symbol (if (name k) (name k) (subs (str k) 1)))
                     v (val ke)]
                 `(~kname (if (contains? ~gkeys ~k) (~gkeys ~k) ~v))))]
    `(defn ~sym [~@ps & k#]
       (let [~gkeys (apply hash-map k#)
             ~@(apply concat (map letk ks))]
         ~@(if pre
             `((assert ~(conj (seq pre) 'and)))
             ())
         (let [res# (do ~@body)]
           ~@(if post
               `((assert ~(conj (map (fn [v] (replace `{% res#} v))
                                      (seq post))
                                'and)))
               ())
           res#)))))




;;; ----------------------------------------------------------------
;;; Some helpers for running external programs.  In particular,
;;; running them while ensuring they actually terminate normally.


;;; The "odd" explicit use of list is the result of a toxic
;;; interaction between syntax-quote not generating lists (but cons
;;; cells) and handler-case not taking this into account.  The bug is
;;; clearly in handler-case as it should account for this
;;;
(defmacro with-handled
  "Wraps FORM in a handler-case with handle case arms for each condition in
   CONDITIONS. Each handle arm catches the condition C and prints a stack trace
   for it.  Hence, while this catches the conditions, it stops execution.
   For catch and continue see CATCH-ALL"
  [form & conditions]
  `(handler-case :type
     ~form
     ~@(map (fn [c] (list 'handle c
                           `(stack-trace-info *condition*)))
            conditions)))


(defmacro with-ckd
  "FORMS wrapped by handlers and last ditch try/catch for standard exceptions.
   For conditions, the condition info meta data map is returned. For exceptions,
   the exception is converted to a string representation and that is returned."
  [& forms]
  `(try
     (do ~@forms)
     (catch clojure.contrib.condition.Condition c#
       (meta c#))
     (catch Exception e#
       (with-out-str
         (print e#)))))


(defmacro catch-all
  "FORMS wrapped by handlers and last ditch try/catch for standard exceptions.
   For conditions, the condition info meta data map is returned. For exceptions,
   the exception is converted to a string representation and that is returned."
  [& forms]
  `(with-ckd ~@forms))



(defn get-tool-path [toolset-type]
  (case toolset-type
        :ncbi
        (or (getenv "NCBI_BLAST")
            "/usr/local/ncbi/blast/bin/")
        :cmfinder
        (or (getenv "CMFINDER")
            "/usr/local/CMFinder/bin/")
        :infernal
        (or (getenv "INFERNAL")
            "/usr/local/Infernal/bin/")

        :cdhit
        (or (getenv "CDHIT")
            "/usr/local/cd-hit/")

        :bioperl "/usr/local/bin/"
        :mysql   "/usr/local/mysql/bin/"))


(defn assert-tools-exist [tool-vec]
  (doseq [pgm (vec tool-vec)]
    (when (not (fs/executable? pgm))
      (let [[_ path p] (re-matches #"(^/.*/)(.*)" pgm)]
        (raise :type :missing-program :path path :pgm p)))))


(defn runx
  "RUNs an eXternal program PROGRAM (a string naming the program executable),
   passing it the (typically, _command line_) arguments ARGS.  ARGS is either
   a single vector or list of the arguments, or a sequential list of the
   arguments given to the function as further arguments after the program."
  [program & args]
  (let [the-args (vec (if (and (= 1 (count args))
                               (sequential? (first args)))
                        (first args)
                        args))

        i (first (seq/positions  #(= :> %1) the-args))
        [the-args stdout] (if (not i)
                            [the-args nil]
                            [(vec (concat (take i the-args)
                                          (subvec the-args (+ 2 i))))
                             (the-args (+ 1 i))])

        i (first (seq/positions #(= :?> %1) the-args))
        [the-args errout] (if (not i)
                            [the-args nil]
                            [(concat (take i the-args)
                                     (subvec the-args (+ 2 i)))
                             (the-args (+ 1 i))])

        result (apply sh program the-args)]

    (when (not= 0 (result :exit))
      (if errout
        (with-open [out (io/writer (io/file-str errout))]
          (binding [*out* out] (print (result :err))))
        (raise :type :program-failed
               :exit (result :exit)
               :pgm program :err (result :err)
               :args the-args)))
    (if stdout
      (with-open [out (io/writer (io/file-str stdout))]
        (binding [*out* out] (print (result :out))))
      (result :out))))
