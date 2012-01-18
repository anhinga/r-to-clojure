(ns RClj.R-be

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
            [clj-shell.shell :as sh]
            [RClj.fs :as fs])
  (:use clojure.contrib.math
        RClj.utils
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
  (let [convert-forms ['Rdouble-array 'double-array int-array float-array]]
    (cond
     (and (sexp? exp) (in (first exp) convert-forms))
     (let [stop (nth exp (if (= (first exp) 'Rdouble-array) 2 1))]
       `(dotimes [~i (int ~stop)]
          ~@body))
     ;; Needs expansion on various other possible R cases...
     :else
     `(doseq [~i ~exp]
        ~@body))))


(defmacro float+ [& args]
  `(double (+ ~@(map #(do `(double ~%)) args))))

(defmacro float- [& args]
  `(double (- ~@(map #(do `(double ~%)) args))))

(defmacro float* [& args]
  `(double (* ~@(map #(do `(double ~%)) args))))

(defmacro float-div [& args]
  `(double (/ ~@(map #(do `(double ~%)) args))))


(defn Rtype [x]
  (cond
   ;; Arrays
   (sexp? x)
   (let [op (first x)]
     (cond
      (in op ['Rdouble-array 'double-array 'float-array 'int-array
              'char-array 'string-array 'make-array])
      (let [tsym (first x)]
        `(:array
          ~(cond
            (in tsym ['Rdouble-array 'double-array 'float-array]) :double
            (= tsym 'int-array) :int
            (= tsym 'char-array) :char
            (= tsym 'string-array) :string
            :else :object)))

      (in op ['float* 'float+ 'float- 'float-div])
      :double

      (= op 'function)
      :function

      :else ; WTF is this?
      'Object))

   (float? x)
   :double

   (integer? x)
   :int

   (char? x)
   :char

   (string? x)
   :string

   :else ; WTF is this???
   'Object))


(defn Rarray-type? [x]
  (and (sexp? x) (= (first x) :array)))

(defn Rfunction-type? [x]
  (= x :function))




;;; This is a _stacking_ scope mechanism.  For the current hack, each
;;; scope maintains
;;;
;;; 1) a set of scope vars (which will become the runtime scope
;;; containers after processing in Rcode-gen) - one each for floats
;;; (actually doubles), ints, char, and strings.  Scope "containers"
;;; are Java arrays (mutable...)  of one of the types double, int,
;;; char, or string.  NOTE: arrays (or other "objects") can just be
;;; implemented with standard Clojure bindings as the arrays are not
;;; assigned - only their _contents_ updated.
;;;
;;; 2) An ordinal count of all the vars for this scope.  This is used
;;; to provide var "binding" ordering and also to provide vars with
;;; their index into their appropriate scope containers
;;;
;;; 3) A map of var packets associated by the var symbol name.  Each
;;; packet contains at least the vars index and type.  These are used
;;; to guide code generation for accessing the var.
;;;
;;; Bound afresh for each call to Rcode-gen
;;;
(def *scopes* (atom :vars))

(defn var-info [vars ord]
  (if (empty? vars)
    [0 nil nil]
    (let [cnt (count vars)
          [vars types] (apply map vector vars)
          ords (take cnt (iterate inc ord))
          infos (map #(do {:index %1 :type %2}) ords types)]
      [cnt vars infos])))


(defn push-scope [& args]
  (let [[cnt vars infos] (var-info args 0)
        vars (if (empty? args) {}
                 (apply hash-map (interleave vars infos)))
        types [:double :int :char :string :float]
        svars (map #(gensym (str (name %) "-vars-")) types)
        scope-vars (apply hash-map (interleave types svars))]
    (swap! *scopes*
           #(cons {:scope scope-vars
                   :ordinal cnt
                   :vars vars}
                  %))))

(defn pop-scope []
  (swap! *scopes* #(rest %)))

(defn add-vars [& vars]
  (let [scope (first @*scopes*)
        [cnt vars infos] (var-info vars (scope :ordinal))
        ordinal (+ (scope :ordinal) cnt)
        vars (apply assoc (scope :vars) (interleave vars infos))]
    (swap! *scopes* #(cons (assoc (first %) :vars vars :ordinal ordinal)
                           (rest %)))))

(defn get-var-scope [x & {info :info :or {info false}}]
  (let [scope (some #(when ((get % :vars) x) %) @*scopes*)]
    (when scope
      (if info
        scope
        (let [vtype (((scope :vars) x) :type)]
          (if (Rarray-type? vtype)
            ;; Arrays are Clj vars bound in enclosing scope (no
            ;; "containers"), so the "scope var" is just x!
            x
            ;; Scalars are container map indexed by var x's type
            ((scope :scope) vtype)))))))

(defn add-var-initval [x initval]
  (let [info (((get-var-scope x :info true) :vars) x)]
    (swap! *scopes* #(cons (assoc-in (first %1) [:vars x :initval] initval)
                           (rest %1)))))

(defn get-var-index [x]
  (let [m (get-var-scope x :info true)]
    (when m (((m :vars) x) :index))))

(defn get-var-type [x]
  (let [m (get-var-scope x :info true)]
    (when m (((m :vars) x) :type))))

(defmacro Rset [x val]
  `(aset ~(get-var-scope x) ~(get-var-index x) ~val))

(defmacro Rget [x]
  (if (Rarray-type? (get-var-type x))
    ;; Arrays are regular Clj vars
    x
    `(aget ~(get-var-scope x) ~(get-var-index x))))


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

   ;; params are a bit odd, but probably shouldn't be.  We can call
   ;; out here or call out function in assignment case and directly
   ;; account for params in that special form.  The latter is the
   ;; better but for this proof of concept hack, just call out here
   ;;
   (= (first sexp) :params)
   (conj (keep cleaner (rest sexp)) :params)

   ;; This case handles situations where you have a primitive sexp at the
   ;; front with its attendant body (which may be null!!
   ;;
   (and (keyword? (first sexp))
        (> (count sexp) 2))
   (let [[k & body] sexp]
     (case k
       :special-form
       (cond

        (= (second (first body)) "return")
        (first (doall (keep cleaner (rest body))))

        (not= (second (first body)) "<-")
        (doall (keep cleaner body))

        :else
        ;; Here we collect all mutated vars for later outer
        ;; scope creation (in driver).  If this var has already been
        ;; collected, insert an assignment for it (Rset ...)
        ;;
        (let [[v exp] (take 2 (drop 1 body))
              v (cleaner v :lhs true)
              exp (cleaner exp)
              exp-type (Rtype exp)]
          (if (and (sexp? v) (= (first v) 'aget))
            ;; An array var, use aset instead
            `(aset ~(nth  v 1) ~(nth v 2) ~exp)
            ;; Else, collect to scope vars and issue assignment for it
            (let [body (drop 3 body) ; move to next exps in this body
                  _ (when-not (get-var-scope v) (add-vars [v exp-type]))
                  setform (macroexpand-1 `(Rset ~v ~exp))]
              (cond
               (Rarray-type? exp-type)
               (do (add-var-initval v exp) nil)

               (Rfunction-type? exp-type)
               (list v exp)

               (seq body)
               (cons setform (keep cleaner body))

               :else
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
         (if (and (get-var-scope x) (not lhs)) (macroexpand-1 `(Rget ~x)) x))

       :op ; these things really should be like :special-form, et.al.
       (case x
         "(" nil
         "{" 'do
         "for" 'Rfor
         "[" 'aget ; Could be used in FOR loop index var analysis
         ":" 'Rdouble-array ; Broken, Needs :f in FOR sets
         "*" 'float*
         "+" 'float+
         "-" 'float-
         "/" 'float-div
         ;; A lot of stuff "subsummed" here that must be dealt with.
         (read-string x))

       :arg ; redundant and messy, just use the actual arg!
       (read-string x)

       :double
       (Double. (double x))))

   :else ; Undoubtedly broken - needs further breakout!
   (keep cleaner sexp)))


(defn Rcode-gen [sexp]
  (binding [*scopes* (atom ())]
    (push-scope)
    (let [raw (cleaner sexp)
          func-name (nth raw 0)
          func-forms (nth raw 1)
          func-params (vec (rest (second func-forms)))
          func-body (rest (nth func-forms 2))

          scope (first @*scopes*)
          cnt (scope :ordinal)
          vars (scope :vars)
          vtypes (reduce (fn[m [k v]]
                           (let [vtype (v :type)]
                             (if (or (Rarray-type? vtype)
                                     (Rfunction-type? vtype))
                               m
                               (assoc m (v :type) true)))) {} vars)
          container-nvs (keep (fn[[k v]]
                                (when (vtypes k)
                                  (let [a (case k
                                            :double `(double-array ~cnt 0.0)
                                            :int (`int-array ~cnt 0)
                                            :float `(float-array ~cnt 0.0)
                                            :char `(char-array ~cnt \space)
                                            :string `(make-array String ~cnt))]
                                    [v a])))
                              (scope :scope))
          array-nvs (keep (fn[[k v]]
                            (when (Rarray-type? (v :type)) [k (v :initval)]))
                          vars)
          [ns vs] (apply map vector (concat container-nvs array-nvs))
          nv-vec (vec (interleave ns vs))

          func-body `(let ~nv-vec
                       ~@func-body)]
      `(defn ~func-name ~func-params ~func-body))))



;;; Yet another hack: set this to the path for where you have R2Sexp.R
;;; front end parser
;;;
(def R2Sexp-path
     "/Users/jonanthony/Clojure/RClj/R2Sexp.R")

(defn R2Sexp-fixed [s]
  (let [R2S R2Sexp-path]
    (read-string
     (re-find #"\[:special.*" (str/replace-re #"\n" "" (runx "Rscript" R2S))))))

(defn Rcompile [x]
  (let [dir (fs/dirname x)
        cpy (fs/join dir "R2Clj-input.R")
        _ (fs/copy x cpy)
        sexp (R2Sexp-fixed cpy)]
    (clojure.lang.Compiler/eval (Rcode-gen sexp))))




;;;(pp/pprint (Rcode-gen *R-poly*))
;;;
;;; A run...
;;;RClj.R-be> (Rcompile *R-poly*)
;;;#'RClj.R-be/trpol2
;;;RClj.R-be> (time (trpol2 5000 0.2))
;;;12500.0"Elapsed time: 9.14068 msecs"
;;;nil
;;;RClj.R-be> (time (trpol2 500000 0.2))
;;;1250000.0"Elapsed time: 902.936831 msecs"
;;;nil