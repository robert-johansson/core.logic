;   Copyright (c) David Nolen, Rich Hickey, contributors. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns core-logic.nbb
  (:refer-clojure :exclude [==])
  (:require [clojure.set :as set]
            [clojure.walk :refer [postwalk]]))

;; =============================================================================
;; Dynamic vars

(def ^:dynamic *logic-dbs* [])
(def ^:dynamic *locals* #{})

;; =============================================================================
;; Protocols

(defprotocol IUnifyTerms
  (-unify-terms [u v s]))

(defprotocol IUnifyWithNil
  (-unify-with-nil [v u s]))

(defprotocol IUnifyWithObject
  (-unify-with-object [v u s]))

(defprotocol IUnifyWithLVar
  (-unify-with-lvar [v u s]))

(defprotocol IUnifyWithLSeq
  (-unify-with-lseq [v u s]))

(defprotocol IUnifyWithSequential
  (-unify-with-seq [v u s]))

(defprotocol IUnifyWithMap
  (-unify-with-map [v u s]))

(defprotocol IReifyTerm
  (-reify-term [v s]))

(defprotocol IWalkTerm
  (-walk-term [v s]))

(defprotocol IOccursCheckTerm
  (-occurs-check-term [v x s]))

(defprotocol IBuildTerm
  (-build-term [u s]))

(defprotocol IBind
  (-bind [this g]))

(defprotocol IMPlus
  (-mplus [a f]))

(defprotocol ITake
  (-take* [a]))

(defprotocol ISubstitutions
  (-occurs-check [this u v])
  (-ext [this u v])
  (-ext-no-check [this u v])
  (-walk [this v])
  (-walk* [this v])
  (-unify [this u v])
  (-reify-lvar-name [_])
  (-reify* [this v])
  (-reify [this v]))

(defprotocol IIfA
  (-ifa [b gs c]))

(defprotocol IIfU
  (-ifu [b gs c]))

(defprotocol LConsSeq
  (-lfirst [this])
  (-lnext [this]))

(defprotocol IUnifyWithPMap
  (unify-with-pmap [pmap u s]))

;; =============================================================================
;; Records

(defrecord LVar [id name])
(defrecord LCons [a d])
(defrecord Substitutions [s meta-map])
(defrecord Choice [a f])
(defrecord Fail [])
(defrecord PMap [])

;; =============================================================================
;; Constructors and predicates

(def lvar-sym-counter (atom 0))

(defn lvar
  ([] (lvar 'gen))
  ([name]
   (let [id (swap! lvar-sym-counter inc)]
     (->LVar id (str name "_" id)))))

(defn ^boolean lvar? [x]
  (instance? LVar x))

(defn ^boolean lcons? [x]
  (instance? LCons x))

(defn lcons
  "Constructs a sequence a with an improper tail d if d is a logic variable."
  [a d]
  (if (and (or (coll? d) (nil? d))
           (not (lvar? d))
           (not (lcons? d)))
    (cons a (seq d))
    (->LCons a d)))

(defn ^boolean failed? [x]
  (instance? Fail x))

(defn ^boolean subst? [x]
  (instance? Substitutions x))

(defn ^boolean pmap? [x]
  (instance? PMap x))

;; =============================================================================
;; Singletons and constants

(declare fail succeed choice empty-s)

(def the-fail (->Fail))

(defn fail
  "A goal that always fails."
  [a] the-fail)

(defn succeed
  "A goal that always succeeds."
  [a] a)

(def s# succeed)
(def u# fail)

(defn make-s
  ([s] (->Substitutions s nil))
  ([s m] (->Substitutions s m)))

(def empty-s (make-s {} nil))

;; Sentinel for walk not-found (identical? on keywords unreliable in SCI extend-type)
(def ^:private walk-not-found #js {})

(defn choice [a f]
  (->Choice a f))

;; =============================================================================
;; LCons helpers

(defn lcons-pr-seq [x]
  (cond
    (lcons? x) (lazy-seq
                 (cons (-lfirst x)
                       (lcons-pr-seq (-lnext x))))
    :else (list '. x)))

;; =============================================================================
;; Stream functions (handle Inc-as-fn before protocol dispatch)

(defn mplus [a f]
  (cond
    (fn? a)           (fn [] (mplus (f) a))  ;; Inc case: swap for interleaving
    (satisfies? IMPlus a) (-mplus a f)
    :else             (choice a f)))

(defn take* [x]
  (cond
    (fn? x)            (lazy-seq (take* (x)))
    (satisfies? ITake x) (-take* x)
    :else              (list x)))

(defn bind [stream g]
  (cond
    (fn? stream)           (fn [] (bind (stream) g))
    (satisfies? IBind stream) (-bind stream g)
    :else                  (g stream)))

;; IIfA / IIfU wrappers that handle Inc-as-fn
(defn ifa [b gs c]
  (cond
    (fn? b)             (fn [] (ifa (b) gs c))
    (satisfies? IIfA b) (-ifa b gs c)
    :else               nil))

(defn ifu [b gs c]
  (cond
    (fn? b)             (fn [] (ifu (b) gs c))
    (satisfies? IIfU b) (-ifu b gs c)
    :else               nil))

;; =============================================================================
;; extend-type Substitutions — ISubstitutions, IBind, IMPlus, ITake, IIfA, IIfU

(extend-type Substitutions
  ISubstitutions
  (-occurs-check [this u v]
    (let [v (-walk this v)]
      (-occurs-check-term v u this)))

  (-ext [this u v]
    (if (and (:occurs-check (:meta-map this))
             (-occurs-check this u v))
      the-fail
      (-ext-no-check this u v)))

  (-ext-no-check [this u v]
    (->Substitutions (assoc (:s this) u v) (:meta-map this)))

  (-walk [this v]
    (if (lvar? v)
      (let [rhs (get (:s this) v walk-not-found)]
        (if (identical? rhs walk-not-found)
          v
          (recur this rhs)))
      v))

  (-walk* [this v]
    (let [v (-walk this v)]
      (-walk-term v this)))

  (-unify [this u v]
    (if (identical? u v)
      this
      (let [u (-walk this u)
            v (-walk this v)]
        (if (identical? u v)
          this
          (if (and (lvar? u) (lvar? v) (= u v))
            this
            (-unify-terms u v this))))))

  (-reify-lvar-name [this]
    (symbol (str "_." (count (:s this)))))

  (-reify* [this v]
    (let [v (-walk this v)]
      (-reify-term v this)))

  (-reify [this v]
    (let [v (-walk* this v)]
      (-walk* (-reify* empty-s v) v)))

  IBind
  (-bind [this g]
    (g this))

  IMPlus
  (-mplus [this f]
    (choice this f))

  ITake
  (-take* [this]
    this)

  IIfA
  (-ifa [b gs c]
    (loop [b b [g0 & gr] gs]
      (if g0
        (when-let [b (g0 b)]
          (recur b gr))
        b)))

  IIfU
  (-ifu [b gs c]
    (loop [b b [g0 & gr] gs]
      (if g0
        (when-let [b (g0 b)]
          (recur b gr))
        b))))

;; =============================================================================
;; extend-type LVar — all unification/walk/reify/occurs-check protocols

(extend-type LVar
  IUnifyTerms
  (-unify-terms [u v s]
    (-unify-with-lvar v u s))

  IUnifyWithNil
  (-unify-with-nil [v u s]
    (-ext-no-check s v u))

  IUnifyWithObject
  (-unify-with-object [v u s]
    (-ext s v u))

  IUnifyWithLVar
  (-unify-with-lvar [v u s]
    (-ext-no-check s u v))

  IUnifyWithLSeq
  (-unify-with-lseq [v u s]
    (-ext s v u))

  IUnifyWithSequential
  (-unify-with-seq [v u s]
    (-ext s v u))

  IUnifyWithMap
  (-unify-with-map [v u s]
    (-ext s v u))

  IReifyTerm
  (-reify-term [v s]
    (-ext s v (-reify-lvar-name s)))

  IWalkTerm
  (-walk-term [v s] v)

  IOccursCheckTerm
  (-occurs-check-term [v x s]
    (= (-walk s v) x)))

;; =============================================================================
;; extend-type LCons — all protocols + LConsSeq

(extend-type LCons
  LConsSeq
  (-lfirst [this] (:a this))
  (-lnext [this] (:d this))

  IUnifyTerms
  (-unify-terms [u v s]
    (-unify-with-lseq v u s))

  IUnifyWithNil
  (-unify-with-nil [v u s] the-fail)

  IUnifyWithObject
  (-unify-with-object [v u s] the-fail)

  IUnifyWithLSeq
  (-unify-with-lseq [v u s]
    (loop [u u v v s s]
      (if (lvar? u)
        (-unify s u v)
        (cond
          (lvar? v) (-unify s v u)
          (and (lcons? u) (lcons? v))
          (let [s (-unify s (-lfirst u) (-lfirst v))]
            (if-not (failed? s)
              (recur (-lnext u) (-lnext v) s)
              s))
          :else (-unify s u v)))))

  IUnifyWithSequential
  (-unify-with-seq [v u s]
    (-unify-with-lseq u v s))

  IUnifyWithMap
  (-unify-with-map [v u s] the-fail)

  IReifyTerm
  (-reify-term [v s]
    (loop [v v s s]
      (if (lcons? v)
        (recur (-lnext v) (-reify* s (-lfirst v)))
        (-reify* s v))))

  IWalkTerm
  (-walk-term [v s]
    (lcons (-walk* s (-lfirst v))
           (-walk* s (-lnext v))))

  IOccursCheckTerm
  (-occurs-check-term [v x s]
    (loop [v v x x s s]
      (if (lcons? v)
        (or (-occurs-check s x (-lfirst v))
            (recur (-lnext v) x s))
        (-occurs-check s x v)))))

;; =============================================================================
;; extend-type Choice — IBind, IMPlus, ITake, IIfA, IIfU

(extend-type Choice
  IBind
  (-bind [this g]
    (mplus (g (:a this)) (fn [] (bind (:f this) g))))

  IMPlus
  (-mplus [this fp]
    (choice (:a this) (fn [] (mplus (fp) (:f this)))))

  ITake
  (-take* [this]
    (lazy-seq (cons (:a this) (lazy-seq (take* (:f this))))))

  IIfA
  (-ifa [b gs c]
    (reduce bind b gs))

  IIfU
  (-ifu [b gs c]
    (reduce bind (:a b) gs)))

;; =============================================================================
;; extend-type Fail — IBind, IMPlus, ITake, IIfA, IIfU

(extend-type Fail
  IBind
  (-bind [this g] this)

  IMPlus
  (-mplus [this fp] fp)

  ITake
  (-take* [this] ())

  IIfA
  (-ifa [b gs c]
    (when c (force c)))

  IIfU
  (-ifu [b gs c]
    (when c (force c))))

;; =============================================================================
;; extend-protocol for nil + default — all unification/walk/reify protocols

;; --- IUnifyTerms ---
(extend-protocol IUnifyTerms
  nil
  (-unify-terms [u v s]
    (-unify-with-nil v u s))

  default
  (-unify-terms [u v s]
    (cond
      (map? u)        (-unify-with-map v u s)
      (sequential? u) (-unify-with-seq v u s)
      :else           (-unify-with-object v u s))))

;; --- IUnifyWithNil ---
(extend-protocol IUnifyWithNil
  nil
  (-unify-with-nil [v u s] s)

  default
  (-unify-with-nil [v u s] the-fail))

;; --- IUnifyWithObject ---
(extend-protocol IUnifyWithObject
  nil
  (-unify-with-object [v u s] the-fail)

  default
  (-unify-with-object [v u s]
    (if (= u v) s the-fail)))

;; --- IUnifyWithLVar ---
(extend-protocol IUnifyWithLVar
  nil
  (-unify-with-lvar [v u s] (-ext-no-check s u v))

  default
  (-unify-with-lvar [v u s] (-ext s u v)))

;; --- IUnifyWithLSeq ---
(extend-protocol IUnifyWithLSeq
  nil
  (-unify-with-lseq [v u s] the-fail)

  default
  (-unify-with-lseq [v u s]
    (if (and (sequential? v) (not (nil? v)))
      (loop [u u v (seq v) s s]
        (if-not (nil? v)
          (if (lcons? u)
            (let [s (-unify s (-lfirst u) (first v))]
              (if-not (failed? s)
                (recur (-lnext u) (next v) s)
                s))
            (-unify s u v))
          (if (lvar? u)
            (-unify s u '())
            the-fail)))
      the-fail)))

;; --- IUnifyWithSequential ---
(extend-protocol IUnifyWithSequential
  nil
  (-unify-with-seq [v u s] the-fail)

  default
  (-unify-with-seq [v u s]
    (if (and (sequential? v) (not (nil? v)))
      (loop [u (seq u) v (seq v) s s]
        (if-not (nil? u)
          (if-not (nil? v)
            (let [s (-unify s (first u) (first v))]
              (if-not (failed? s)
                (recur (next u) (next v) s)
                s))
            the-fail)
          (if-not (nil? v) the-fail s)))
      the-fail)))

;; --- IUnifyWithMap ---
(defn unify-with-map* [v u s]
  (if-not (clojure.core/== (count v) (count u))
    the-fail
    (loop [ks (seq (keys u)) s s]
      (if ks
        (let [kf (first ks)
              vf (get v kf ::not-found)]
          (if (identical? vf ::not-found)
            the-fail
            (let [s (-unify s (get u kf) vf)]
              (if-not (failed? s)
                (recur (next ks) s)
                the-fail))))
        s))))

(extend-protocol IUnifyWithMap
  nil
  (-unify-with-map [v u s] the-fail)

  default
  (-unify-with-map [v u s]
    (if (map? v)
      (unify-with-map* v u s)
      the-fail)))

;; --- IReifyTerm ---
(extend-protocol IReifyTerm
  nil
  (-reify-term [v s] s)

  default
  (-reify-term [v s]
    (if (sequential? v)
      (loop [v v s s]
        (if (seq v)
          (recur (next v) (-reify* s (first v)))
          s))
      s)))

;; --- IWalkTerm ---
(defn walk-term-map* [v s]
  (into {} (map (fn [[k val]] [k (-walk* s val)]) v)))

(extend-protocol IWalkTerm
  nil
  (-walk-term [v s] nil)

  default
  (-walk-term [v s]
    (cond
      (vector? v) (into [] (map #(-walk* s %) v))
      (map? v)    (walk-term-map* v s)
      (sequential? v) (map #(-walk* s %) v)
      :else v)))

;; --- IOccursCheckTerm ---
(extend-protocol IOccursCheckTerm
  nil
  (-occurs-check-term [v x s] false)

  default
  (-occurs-check-term [v x s]
    (if (sequential? v)
      (loop [v (seq v) x x s s]
        (if-not (nil? v)
          (or (-occurs-check s x (first v))
              (recur (next v) x s))
          false))
      false)))

;; =============================================================================
;; Substitution helpers

(defn to-s [v]
  (make-s (into {} (map (fn [[k val]] [k val]) v))))

;; =============================================================================
;; Macros — defined inline for nbb/SCI

;; -inc: creates a thunk (Inc replacement)
(defmacro -inc [& body]
  `(fn [] ~@body))

;; == : unification goal
(defmacro == [u v]
  `(fn [a#]
     (if-let [b# (-unify a# ~u ~v)]
       b# (fail a#))))

;; bind* : chain bindings
(defmacro bind*
  ([a g] `(bind ~a ~g))
  ([a g & g-rest]
   `(bind* (bind ~a ~g) ~@g-rest)))

;; mplus* : chain mplus with Inc thunks
(defmacro mplus*
  ([e] e)
  ([e & e-rest]
   `(mplus ~e (-inc (mplus* ~@e-rest)))))

;; fresh : introduce logic variables and conjoin goals
(defn- lvar-bind [sym]
  ((juxt identity
         (fn [s] `(lvar '~s))) sym))

(defn- lvar-binds [syms]
  (mapcat lvar-bind syms))

(defmacro fresh
  [[& lvars] & goals]
  `(fn [a#]
     (-inc
       (let [~@(lvar-binds lvars)]
         (bind* a# ~@goals)))))

;; conde : logical disjunction with interleaving
(defn- bind-conde-clause [a]
  (fn [g-rest]
    `(bind* ~a ~@g-rest)))

(defn- bind-conde-clauses [a clauses]
  (map (bind-conde-clause a) clauses))

(defmacro conde
  [& clauses]
  (let [a (gensym "a")]
    `(fn [~a]
       (-inc
         (mplus* ~@(bind-conde-clauses a clauses))))))

;; -run : core run implementation
(defmacro -run [opts [x :as bindings] & goals]
  (if (> (count bindings) 1)
    (let [[rbindings as-key [as]] (partition-by #{:as} bindings)]
      (if (seq as-key)
        `(-run ~opts [~as] (fresh [~@rbindings] (== ~as [~@rbindings]) ~@goals))
        `(-run ~opts [q#] (fresh ~bindings (== q# ~bindings) ~@goals))))
    `(let [opts# ~opts
           xs# (take*
                 (-inc
                   ((fresh [~x] ~@goals
                      (fn [a#]
                        (-reify a# ~x)))
                    (assoc empty-s :meta-map
                      (merge {:reify-vars true} opts#)))))]
       (if-let [n# (:n opts#)]
         (take n# xs#)
         xs#))))

(defmacro run
  [n bindings & goals]
  `(-run {:occurs-check true :n ~n :db *logic-dbs*}
     ~bindings ~@goals))

(defmacro run*
  [bindings & goals]
  `(-run {:occurs-check true :n false :db *logic-dbs*}
     ~bindings ~@goals))

(defmacro run-db
  [n db bindings & goals]
  `(-run {:occurs-check true :n ~n :db (flatten [~db])} ~bindings ~@goals))

(defmacro run-db*
  [db bindings & goals]
  `(-run {:occurs-check true :n false :db (flatten [~db])} ~bindings ~@goals))

(defmacro run-nc
  [n bindings & goals]
  `(-run {:occurs-check false :n ~n :db *logic-dbs*} ~bindings ~@goals))

(defmacro run-nc*
  [& goals]
  `(run-nc false ~@goals))

(defmacro all
  ([] `s#)
  ([& goals] `(fn [a#] (bind* a# ~@goals))))

;; =============================================================================
;; Debugging macros

(defmacro log
  [& s]
  `(fn [a#]
     (println ~@s)
     a#))

(defmacro trace-s
  []
  `(fn [a#]
     (println (str a#))
     a#))

(defn- trace-lvar [a lvar]
  `(println (str '~lvar " = " (-reify ~a ~lvar))))

(defmacro trace-lvars
  [title & lvars]
  (let [a (gensym "a")]
    `(fn [~a]
       (println ~title)
       ~@(map (partial trace-lvar a) lvars)
       ~a)))

;; =============================================================================
;; Non-relational goals

(defn- project-binding [s]
  (fn [var]
    `(~var (-walk* ~s ~var))))

(defn- project-bindings [vars s]
  (reduce concat (map (project-binding s) vars)))

(defmacro project
  [[& vars] & goals]
  (let [a (gensym "a")]
    `(fn [~a]
       (let [~@(project-bindings vars a)]
         ((fresh []
            ~@goals) ~a)))))

(defmacro pred
  [v f]
  `(project [~v]
     (== (~f ~v) true)))

(defmacro is
  [u v op]
  `(project [~v]
     (== ~u (~op ~v))))

;; =============================================================================
;; conda / condu (soft-cut, committed-choice)

(defn- cond-clauses [a]
  (fn [goals]
    `((~(first goals) ~a) ~@(rest goals))))

(defmacro ifa*
  ([] nil)
  ([[e & gs] & grest]
   `(ifa ~e [~@gs]
      ~(if (seq grest)
         `(delay (ifa* ~@grest))
         nil))))

(defmacro ifu*
  ([] nil)
  ([[e & gs] & grest]
   `(ifu ~e [~@gs]
      ~(if (seq grest)
         `(delay (ifu* ~@grest))
         nil))))

(defmacro conda
  [& clauses]
  (let [a (gensym "a")]
    `(fn [~a]
       (ifa* ~@(map (cond-clauses a) clauses)))))

(defmacro condu
  [& clauses]
  (let [a (gensym "a")]
    `(fn [~a]
       (ifu* ~@(map (cond-clauses a) clauses)))))

;; =============================================================================
;; lvaro / nonlvaro

(defmacro lvaro
  [v]
  `(fn [a#]
     (if (lvar? (-walk a# ~v))
       a# nil)))

(defmacro nonlvaro
  [v]
  `(fn [a#]
     (if (not (lvar? (-walk a# ~v)))
       a# nil)))

;; =============================================================================
;; Pattern matching

(declare p->term)

(defn lcons-p? [p]
  (and (coll? p)
       (not (nil? (some '#{.} p)))))

(defn p->llist [p]
  `(llist
    ~@(map p->term
           (remove #(contains? '#{.} %) p))))

(defn p->term [p]
  (cond
    (= p '_) `(lvar)
    (lcons-p? p) (p->llist p)
    (and (coll? p) (not= (first p) 'quote))
    (cond
      (list? p) p
      (map? p) (into {} (map (fn [[k v]] [(p->term k) (p->term v)]) p))
      (vector? p) (into [] (map p->term p))
      (set? p) (into #{} (map p->term p))
      :else (into (empty p) (map p->term p)))
    :else p))

(defn lvar-sym? [s]
  (and (symbol? s)
       (not= s '.)
       (not (contains? *locals* s))))

(defn extract-vars
  ([p]
   (set (cond
          (lvar-sym? p) [p]
          (coll? p) (let [p (if (seq? p) (rest p) p)]
                      (filter lvar-sym? (flatten p)))
          :else nil)))
  ([p seen]
   (set/difference (extract-vars p) (set seen))))

(defn fresh-expr? [cs]
  (= (first cs) `fresh))

(defn ex
  ([vs t a]
   `(fresh [~@vs]
      (== ~t ~a)))
  ([vs t a exprs]
   (if (fresh-expr? exprs)
     `(fresh [~@vs]
        (== ~t ~a)
        ~exprs)
     `(fresh [~@vs]
        (== ~t ~a)
        ~@exprs))))

(defn ex* [[[p a :as pa] & par] exprs seen]
  (let [t (p->term p)
        vs (extract-vars p seen)
        seen (reduce conj seen vs)]
    (cond
      (nil? pa) exprs
      (= p '_) (ex* par exprs seen)
      (empty? par) (if exprs
                     (ex vs t a exprs)
                     (ex vs t a))
      :else (let [r (ex* par exprs seen)]
              (if r
                (ex vs t a r)
                (ex vs t a))))))

(defn all-blank? [p]
  (every? #(= % '_) p))

(defn handle-clause [as]
  (fn [[p & exprs]]
    (let [pas (partition 2 (interleave p as))
          r (ex* pas exprs #{})]
      (if (all-blank? p)
        r
        (list r)))))

(defn handle-clauses [t as cs]
  `(~t
    ~@(doall (map (handle-clause as) cs))))

(defn name-with-attributes
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
                                 attr)]
    [(with-meta name attr) macro-args]))

(defn env-locals [& syms]
  (disj (set (apply concat syms)) '_))

;; llist macro
(defmacro llist
  ([f s] `(lcons ~f ~s))
  ([f s & rest] `(lcons ~f (llist ~s ~@rest))))

;; Pattern matching macros
(defmacro -fnm [fn-gen t as & cs]
  (binding [*locals* (env-locals as)]
    `(~fn-gen [~@as] ~(handle-clauses t as cs))))

(defmacro fnm
  [t as & cs]
  (if-let [cs (and (= (first cs) :tabled) (rest cs))]
    `(-fnm tabled ~t ~as ~@cs)
    `(-fnm fn ~t ~as ~@cs)))

(defmacro defnm [t n & rest]
  (let [[n [as & cs]] (name-with-attributes n rest)
        e (if (-> n meta :tabled)
            `(fnm ~t ~as :tabled ~@cs)
            `(fnm ~t ~as ~@cs))]
    `(def ~n ~e)))

(defmacro fne [& rest]
  `(fnm conde ~@rest))

(defmacro defne [& rest]
  `(defnm conde ~@rest))

(defmacro matche [xs & cs]
  (binding [*locals* (env-locals xs (keys &env))]
    (handle-clauses `conde xs cs)))

(defmacro fna [& rest]
  `(fnm conda ~@rest))

(defmacro fnu [& rest]
  `(fnm condu ~@rest))

(defmacro defna [& rest]
  `(defnm conda ~@rest))

(defmacro defnu [& rest]
  `(defnm condu ~@rest))

(defmacro matcha [xs & cs]
  (binding [*locals* (env-locals xs (keys &env))]
    (handle-clauses `conda xs cs)))

(defmacro matchu [xs & cs]
  (binding [*locals* (env-locals xs (keys &env))]
    (handle-clauses `condu xs cs)))

;; =============================================================================
;; Built-in relations

(defn nilo
  "A relation where a is nil"
  [a]
  (== nil a))

(defn emptyo
  "A relation where a is the empty list"
  [a]
  (== '() a))

(defn conso
  "A relation where l is a collection, such that a is the first of l
  and d is the rest of l"
  [a d l]
  (== (lcons a d) l))

(defn firsto
  "A relation where l is a collection, such that a is the first of l"
  [l a]
  (fresh [d]
    (conso a d l)))

(defn resto
  "A relation where l is a collection, such that d is the rest of l"
  [l d]
  (fresh [a]
    (== (lcons a d) l)))

(defne membero
  "A relation where l is a collection, such that l contains x"
  [x l]
  ([_ [x . tail]])
  ([_ [head . tail]]
   (membero x tail)))

(defne appendo
  "A relation where x, y, and z are proper collections,
  such that z is y appended to x"
  [x y z]
  ([() _ y])
  ([[a . d] _ [a . r]] (appendo d y r)))

;; =============================================================================
;; Utilities

(defn prefix [s <s]
  (if (= s <s)
    ()
    (conj (prefix (rest s) <s) (first s))))

(defn to-stream [aseq]
  (let [aseq (drop-while nil? aseq)]
    (if (seq aseq)
      (choice (first aseq)
        (fn [] (to-stream (next aseq))))
      the-fail)))

;; =============================================================================
;; Partial maps

(extend-type PMap
  IUnifyWithMap
  (-unify-with-map [v u s]
    (loop [ks (keys v) s s]
      (if (seq ks)
        (let [kf (first ks)
              uf (get u kf ::not-found)]
          (if (= uf ::not-found)
            the-fail
            (let [s (-unify s (get v kf) uf)]
              (if-not (failed? s)
                (recur (next ks) s)
                s))))
        s)))

  IUnifyWithPMap
  (unify-with-pmap [v u s]
    (-unify-with-map v u s))

  IUnifyTerms
  (-unify-terms [u v s]
    (unify-with-pmap v u s))

  IUnifyWithLVar
  (-unify-with-lvar [v u s]
    (-ext-no-check s u v))

  IWalkTerm
  (-walk-term [v s]
    (walk-term-map* v s)))

(extend-protocol IUnifyWithPMap
  nil
  (unify-with-pmap [v u s] the-fail)

  default
  (unify-with-pmap [v u s]
    (cond
      (lvar? v) (-ext s v u)
      (map? v)  (-unify-with-map u v s)
      :else     the-fail)))

(defn partial-map
  "Given map m, returns partial map that unifies with maps even if it
  doesn't share all of the keys of that map."
  [m]
  (map->PMap m))

;; =============================================================================
;; Easy Unifier

(defn- lvarq-sym? [s]
  (and (symbol? s) (= (first (str s)) \?)))

(defn- proc-lvar [lvar-expr store]
  (let [v (if-let [u (@store lvar-expr)]
            u
            (lvar lvar-expr))]
    (swap! store conj [lvar-expr v])
    v))

(defn- lcons-expr? [expr]
  (and (seq? expr) (some '#{.} (set expr))))

(declare prep*)

(defn- replace-lvar [store]
  (fn [expr]
    (if (lvarq-sym? expr)
      (proc-lvar expr store)
      (if (lcons-expr? expr)
        (prep* expr store)
        expr))))

(defn- prep*
  ([expr store] (prep* expr store false false))
  ([expr store lcons?] (prep* expr store lcons? false))
  ([expr store lcons? last?]
   (let [expr (if (and last? (seq expr))
                (first expr)
                expr)]
     (cond
       (lvarq-sym? expr) (proc-lvar expr store)
       (seq? expr) (if (or lcons? (lcons-expr? expr))
                     (let [[f & n] expr
                           skip (= f '.)
                           tail (prep* n store lcons? skip)]
                       (if skip
                         tail
                         (lcons (prep* f store) tail)))
                     (postwalk (replace-lvar store) expr))
       :else expr))))

(defn prep
  "Prep a quoted expression. All symbols preceded by ? will
  be replaced with logic vars."
  [expr]
  (let [lvars (atom {})
        prepped (if (lcons-expr? expr)
                  (prep* expr lvars true)
                  (postwalk (replace-lvar lvars) expr))]
    (with-meta prepped {:lvars @lvars})))

(defn unify [s u v]
  (if (identical? u v)
    s
    (let [u (-walk s u)
          v (-walk s v)]
      (if (identical? u v)
        s
        (-unify-terms u v s)))))

(defn unifier*
  "Unify the terms u and w."
  ([u w]
   (first
     (run* [q]
       (== u w)
       (== u q))))
  ([u w & ts]
   (apply unifier* (unifier* u w) ts)))

(defn binding-map*
  "Return the binding map that unifies terms u and w.
  u and w should be prepped terms."
  ([u w]
   (let [lvars (merge (-> u meta :lvars)
                      (-> w meta :lvars))
         s (unify empty-s u w)]
     (when-not (failed? s)
       (into {} (map (fn [[k v]]
                       [k (-reify s v)])
                     lvars)))))
  ([u w & ts]
   (apply binding-map* (binding-map* u w) ts)))

(defn unifier
  "Unify the terms u and w. Will prep the terms."
  ([u w]
   {:pre [(not (lcons? u))
          (not (lcons? w))]}
   (let [up (prep u)
         wp (prep w)]
     (unifier* up wp)))
  ([u w & ts]
   (apply unifier (unifier u w) ts)))

(defn binding-map
  "Return the binding map that unifies terms u and w.
  Will prep the terms."
  ([u w]
   {:pre [(not (lcons? u))
          (not (lcons? w))]}
   (let [up (prep u)
         wp (prep w)]
     (binding-map* up wp)))
  ([u w & ts]
   (apply binding-map (binding-map u w) ts)))
