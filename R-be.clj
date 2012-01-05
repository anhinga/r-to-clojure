(ns edu.bc.bio.R-be

  "R to Clojure compiler backend.  The current frontend is in R and
   generates an AST in sexp form.  The AST actually uses vectors
   instead of lists, for easier input to Clojure."

  (:require [clojure.contrib.math :as math]
            [clojure.contrib.string :as str]
            [clojure.contrib.str-utils :as stru]
            [clojure.contrib.pprint :as pp]
            [clojure.set :as set]
            [clojure.contrib.seq :as seq]
            [clojure.zip :as zip]
            [clojure.contrib.io :as io]
            [clj-shell.shell :as sh])
  (:use clojure.contrib.math
        edu.bc.utils
        [clojure.contrib.condition
         :only (raise handler-case *condition* print-stack-trace)]
        [clojure.contrib.pprint
         :only (cl-format compile-format)]
        ))



(defn gen-suffixes [sq]
  (let [bits (reverse (seq sq))
        len (inc (count bits))]
    (loop [i 1
           suffixes []]
      (if (= i len)
        (map reverse suffixes)
        (recur (inc i)
               (conj suffixes (take i bits)))))))




;;; Primary test AST as output from R Front End parser
;;;
(def *R-poly*
     [:special-form [:op "<-"] [:symbol "trpol2"] [:special-form [:op "function"] [:params [:arg "n"] [:arg "x"]] [:special-form [:op "{"] [:special-form [:op "<-"] [:symbol "mu"] [:double 10]] [:special-form [:op "<-"] [:symbol "pu"] [:double 0]] [:special-form [:op "<-"] [:symbol "pol"] [:call-builtin [:op ":"] [:double 1] [:double 100]]] [:special-form [:op "<-"] [:symbol "tp1"] [:double 2]] [:special-form [:op "<-"] [:symbol "tm1"] [:call-builtin [:op "/"] [:double 1] [:double 2]]] [:special-form [:op "for"] [:symbol "i"] [:call-builtin [:op ":"] [:double 1] [:symbol "n"]] [:special-form [:op "{"] [:special-form [:op "for"] [:symbol "j"] [:call-builtin [:op ":"] [:double 1] [:double 100]] [:special-form [:op "{"] [:special-form [:op "<-"] [:symbol "mu"] [:call-builtin [:op "*"] [:call-builtin [:op "("] [:call-builtin [:op "+"] [:symbol "mu"] [:symbol "tp1"]]] [:symbol "tm1"]]] [:special-form [:op "<-"] [:special-form [:op "["] [:symbol "pol"] [:symbol "j"]] [:symbol "mu"]]]] [:special-form [:op "<-"] [:symbol "s"] [:double 0]] [:special-form [:op "for"] [:symbol "j"] [:call-builtin [:op ":"] [:double 1] [:double 100]] [:special-form [:op "{"] [:special-form [:op "<-"] [:symbol "s"] [:call-builtin [:op "+"] [:call-builtin [:op "*"] [:symbol "x"] [:symbol "s"]] [:special-form [:op "["] [:symbol "pol"] [:symbol "j"]]]]]] [:special-form [:op "<-"] [:symbol "pu"] [:call-builtin [:op "+"] [:symbol "s"] [:symbol "pu"]]]]] [:call-closure [:symbol "print"] [:symbol "pu"]]] []]])




(def +R-ns+ (find-ns 'edu.bc.bio.R-be))

(defn sexp? [x]
  (or (vector? x)
      (seq? x)))


(defn fold-forms
  "Currently not used and frankly a crappy hack in the first place!
  So, when we push more toward a pure functional variant, this will
  need replacing anyway!"

  [sexp]

  (if (not (sexp? sexp))
    sexp
    (let [hd (first sexp)
          tail (rest sexp)
          next-form (first tail)]
      ;;(prn hd) (prn tail) (prn next-form)
      (cond
       (= hd 'function)
       (let [params next-form
             body (rest tail)]
         ;;(prn params body)
         `(function ~params ~@(map fold-forms body)))

       (= hd 'do)
       (if (and (sexp? next-form)
                (= (first next-form) 'clojure.core/let))
         (fold-forms tail)
         (cons 'do (fold-forms tail)))

       (and (sexp? hd)
            (= (first hd) 'clojure.core/let))
       (if (and (sexp? next-form)
                (= (first next-form) 'clojure.core/let))
         (let [[b1 & t1] (rest hd)
               [b2 & t2] (rest next-form)]
           ;;(prn :>>) (prn b1 t1) (prn b2 t2)
           (fold-forms
            (cons
             `(let ~(vec (concat (fold-forms b1) (fold-forms b2)))
                ~@(fold-forms t1)
                ~@(fold-forms t2))
             (list (fold-forms (rest tail))))))
         ;;else
         (do ;(println "\n" :*** tail)
             (concat hd (fold-forms tail))))

       :else
       (let [folded (map fold-forms sexp)]
         (if (vector? sexp)
           (vec folded)
           folded))))))



;;; A palette macro for making insane R array definitions a little
;;; more sane w/o front end parser support.
;;;
(defmacro Rdouble-array [& args]
  `(double-array (int ~(second args)) ~(first args)))


;;; This really needs to be made better - currently _realizes_ the
;;; java array as a seq and then moves over that. UGH!
;;;
(defmacro Rfor [i exp & body]
    `(doseq [~i ~exp]
       ~@body)))


;;; The intent here is that this could be a _stacking_ scope
;;; mechanism.  Currently it does NOT do that, but easily could be
;;; changed to do that.
;;;
;;; Bound afresh for each call to Rcode-gen
;;;
(def *scopes* :vars)


;;; This has mutated to be more than just a cleanup pass.  Which means
;;; that it should be refactored!  Currently it also does most of the
;;; code generation as well.  So, it isn't even named correctly
;;; anymore!!
;;;
(defn cleaner [sexp & {lhs :lhs :or {lhs false}}]
  ;;(prn :*** sexp)
  (cond

   (= 0 (count sexp)) ; get rid of empty blocks
   nil

   ;; This case handles situations where you have a primitive sexp at the
   ;; front with its attendant body (which may be null!!
   ;;
   (and (keyword? (first sexp))
        (> (count sexp) 2))
   (let [[k & body] sexp]
     (case k
       :special-form
       (if (not= (second (first body)) "<-")
         (doall (keep cleaner body))

         ;; Else, here we collect all mutated vars for later outer
         ;; scope creation (in driver).  If this var has already been
         ;; collected, insert an assignment for it (var-set ...)
         ;;
         (let [[v exp] (take 2 (drop 1 body))
               v (cleaner v :lhs true)
               exp (cleaner exp)]
           (if (and (sexp? v) (= (first v) 'aget))
             ;; An array var, use aset instead
             `(aset ~(nth  v 1) ~(nth v 2) ~exp)
             ;; Else, collect to scope vars and issue assignment for it
             (let [body (drop 3 body) ; move to next exps in this body
                   setform `(var-set ~v ~exp)]
               (when-not (get @*scopes* v)
                 (swap! *scopes* #(assoc %1 %2 [(gen-uid) exp]) v))
               (if (seq body)
                 (cons setform (keep cleaner body))
                 setform)))))

       :call-closure
       (doall (keep cleaner body))

       :call-builtin
       (let [res (doall (keep cleaner body))]
         ;; Get rid of bizarre paren "op" effects
         (if (= (first body) [:op "("]) (first res) res))

       :params
       (conj (keep cleaner body) :params)))

   ;; This case is basically the simple primitive sexps denoting
   ;; primitive elements (symbols, ops, etc.)
   ;;
   (and (keyword? (first sexp))
        (= (count sexp) 2))
   (let [[k x] sexp]
     (case k
       :symbol
       (let [x (read-string x)]
         (if (and (get @*scopes* x) (not lhs)) `(var-get ~x) x))

       :op ; these things really should be like :special-form, et.al.
       (case x
         "(" nil
         "{" 'do
         "for" 'Rfor
         "[" 'aget ; Could be used in FOR loop index var analysis
         ":" 'Rdouble-array ; Broken, Needs :f in FOR sets
         ;; A lot of stuff "subsummed" here that must be dealt with.
         (read-string x))

       :arg ; redundant and messy, just use the actual arg!
       (read-string x)

       :double
       (Double. (double x))))

   :else ; Undoubtedly broken - needs further breakout!
   (keep cleaner sexp)))


(defn Rcode-gen [sexp]
  (binding [*scopes* (atom {})]
    (let [raw (cleaner sexp)
          func-name (nth raw 1)
          func-forms (nth raw 2)
          func-params (vec (rest (second func-forms)))
          func-body (rest (nth func-forms 2))
          nv-map (reduce (fn[m [k v]] (assoc m k v)) {}
                         (map (fn[[k [o v]]] [k v])
                              (sort-by (fn[[k v]] (first v))
                                       (dissoc @*scopes* func-name))))
          nv-vec (vec (interleave (keys nv-map) (vals nv-map)))
          func-body `(with-local-vars ~nv-vec
                       ~@func-body)]
      `(defn ~func-name ~func-params ~func-body))))




(pp/pprint (Rcode-gen *R-poly*))

;;; Yields the following (though this is manually cleaned up wrt code
;;; alignment and explicit clojure.core name space prefixes removed
;;;
(defn trpol2 [n x]
  (with-local-vars
      [s 0.0
       tm1 (/ 1.0 2.0)
       tp1 2.0
       pol (Rdouble-array 1.0 100.0)
       pu 0.0
       mu 10.0]
    (var-set mu 10.0)
    (var-set pu 0.0)
    (var-set pol (Rdouble-array 1.0 100.0))
    (var-set tp1 2.0)
    (var-set tm1 (/ 1.0 2.0))
    (Rfor i (Rdouble-array 1.0 n)
          (do (Rfor j (Rdouble-array 1.0 100.0)
                    (do (var-set mu (* (+ (var-get mu) (var-get tp1))
                                       (var-get tm1)))
                        (aset (var-get pol) j (var-get mu))))
              (var-set s 0.0)
              (Rfor j (Rdouble-array 1.0 100.0)
                    (do (var-set s (+ (* x (var-get s))
                                      (aget (var-get pol) j)))))
              (var-set pu (+ (var-get s) (var-get pu)))))
    (print (var-get pu))))

;;; A run:
edu.bc.bio.R-be> (time (trpol2 5000 0.2))
12500.0"Elapsed time: 14049.346975 msecs"
nil


;;; ----------  Experiments and interactive fooling around below ------

(def +branches+ [:special-form :call-closure :call-builtin :params])


(defn array? [x] (-> x class .isArray))
(defn look-at [x] (if (array? x) (map look-at x) x))

(look-at (make-array Float/TYPE 100))
(look-at (into-array Float/TYPE [1 2 3 4 5 6 7 8 9 10]))


(defmacro %aget
  ([hint array idx]
    `(aget ~(vary-meta array assoc :tag hint) (int ~idx)))
  ([hint array idx & idxs]
    `(let [a# (aget ~(vary-meta array assoc :tag 'objects) (int ~idx))]
       (%aget ~hint a# ~@idxs))))

(defmacro %aset [hint array & idxsv]
  (let [hints '{floats float doubles double ints int}
        [v idx & sxdi] (reverse idxsv)
        idxs (reverse sxdi)
        v (if-let [h (hints hint)] (list h v) v)
        nested-array (if (seq idxs)
                       `(%aget ~'objects ~array ~@idxs)
                        array)
        a-sym (with-meta (gensym "a") {:tag hint})]
      `(let [~a-sym ~nested-array]
         (aset ~a-sym (int ~idx) ~v))))


(def sfa (make-array Float/TYPE 1000000))

(%aget floats sfa 9)
(%aset floats sfa 9 Math/E)
(%aset floats sfa 9 Math/PI)
(%aget floats sfa (int 9))

(defn #^Float xx [#^Float x #^Float y]
  (+ (float x) (float y)))

(defn yy [#^Float x #^Float y]
  (+ (float x) (float y)))

(defn foo [x y]
  (+ (float 4.5) (yy x y)))


(defn dopoly [x]
  (let [cnt 100
        pol (




(defn #^Float dopoly [#^Float x]
  (let [x (float x)
        cnt (int 100)
        pol (make-array Float/TYPE 100)]
    (loop [j (int 0)
           mu (float 10.0)]
        (when (< j cnt)
          (%aset floats pol j (/ (+ mu (float 2.0)) (float 2.0)))
          (recur (unchecked-inc j)
                 (%aget floats pol j))))
    (loop [j (int 0)
           su (float 0.0)]
        (if (< j cnt)
          (recur (unchecked-inc j)
                 (+ (%aget floats pol j) (* su x)))
          su))))


(defn eval-pol [polfn #^Integer n #^Float x]
  (let [n (int n)
        x (float x)]
    (loop [i (int 0)
           pu (float 0.0)]
      (if (< i n)
        (recur (unchecked-inc i)
               (+ pu (float (polfn x))))
        pu))))


(defn eval-pol-par [polfn #^Integer n #^Float x & {par :par :or {par 10}}]
  (let [n (int n)
        q (math/floor (/ n par))
        r (rem n 10)
        chunks (conj (repeat (dec par) q) (+ q r))]
    (reduce #(+ (float %1) (float %2))
            (float 0.0)
            (pmap #(eval-pol polfn % x) chunks))))



(map #(do [% (+ % 1000000 -1)])
     (take 10 (iterate #(+ % 1000000) 1)))



(defn div-3-5 [n] (or (= 0 (rem n 3)) (= 0 (rem n 5))))

(defn check-chunk [s e]
  (count (filter div-3-5 (range s (inc e)))))

(defn par-count []
  (reduce
   + 0 (pmap (fn[[x y]] (check-chunk x y))
             (map #(do [% (+ % 1000000 -1)])
                  (take 10 (iterate #(+ % 1000000) 1))))))


;-----------------------
;(floats (make-array Float/TYPE 100))

(defn #^Float dopoly-simon [#^Float x]
  (let [x (float x)
        cnt (int 100)
        pol (float-array 100)]
    (loop [j (int 0)
           mu (float 10.0)]
      (when (< j cnt)
        (aset pol j (/ (+ mu (float 2.0)) (float 2.0)))
        (recur (unchecked-inc j)
               (float (aget pol j)))))
    (loop [j (int 0)
           su (float 0.0)]
      (if (< j cnt)
        (recur (unchecked-inc j)
               (float (+ (aget pol j) (* su x))))
        su))))


(defn eval-pol-simon [#^Integer n #^Float x]
  (let [n (int n)
        x (float x)]
    (loop [i (int 0)
           pu (float 0.0)]
      (if (< i n)
        (recur (unchecked-inc i)
               (+ pu (float (dopoly-simon x))))
        pu))))


(defn eval-pol-par-simon [#^Integer n #^Float x & {par :par :or {par 10}}]
  (let [n (int n)
        q (Math/floor (/ n par))
        r (rem n 10)
        chunks (conj (repeat (dec par) q) (+ q r))]
    (reduce #(+ (float %1) (float %2))
            (float 0.0)
            (pmap #(eval-pol-simon % x) chunks))))


(defn dopoly-idiomatic [x]
  (let [cnt 100
        pol (float-array 100)]
    (loop [j 0
           mu (float 10.0)]
      (when (< j cnt)
        (aset pol j (float (/ (+ mu 2.0) 2.0)))
        (recur (inc j)
               (float (aget pol j)))))
    (loop [j 0
           su (float 0.0)]
      (if (< j cnt)
        (recur (inc j)
               (float (+ (aget pol j) (* su x))))
        su))))


(defn dopoly-functional [x]
  (let [cnt 100
        pol (vector (repeat 100 0.0))
        pol (loop [j 0
                   mu 10.0
                   pol pol]
              (if (>= j cnt)
                pol
                (let [v (float (/ (+ mu 2.0) 2.0))]
                  (recur (inc j)
                         v
                         (assoc pol j v)))))]
    (loop [j 0
           su 0.0]
      (if (< j cnt)
        (recur (inc j)
               (+ (pol j) (* su x)))
        su))))

