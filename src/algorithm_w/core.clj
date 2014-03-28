(ns algorithm-w.core
  (:refer-clojure :exclude [reify])
  (:use [clojure.core.match :only (match)]
        [clojure.set :only (union difference)]
        [clojure.walk :only (postwalk postwalk-replace)]))

;;; free type variable

(defn ftv [t]
  (match t
    (_ :guard symbol?)    #{t}
    (_ :guard map?)       (apply union (map ftv (vals t)))
    ([t1 '-> t2] :seq)    (union (ftv t1) (ftv t2))
    ([:forall v t*] :seq) (difference (ftv t*) v)
    ([& xs] :seq)         (apply union (map ftv xs))
    :else                 #{}))

(defn fresh [] (gensym "__type__"))

;;; substitution

(defn mapval [f m]
  (into {} (for [[k v] m] [k (f v)])))

(defn subst [S t]
  (match t
    (_ :guard map?)       (mapval #(subst S %) t)
    ([t1 '-> t2] :seq)    (list (subst S t1) '-> (subst S t2))
    ([:forall v t*] :seq) (list :forall v (subst (dissoc S v) t*))
    :else                 (postwalk-replace S t)))

(defn compose
  "Compose type substitutions, right-to-left, i.e. should have
   apply (compose s1 s2) t = apply s1 (apply s2 t)"
  ([s1 s2]
   (when (and s1 s2) (merge (subst s1 s2) s1)))
  ([s1 s2 & more]
   (compose s1 (apply compose (cons s2 more)))))

;;; generalize/instantiate

(defn generalize [v env]
  [:forall (difference (ftv v) (ftv env)) v])

(defn instantiate [t]
  (match t
    ([:forall v t*] :seq)
    (let [S (into {} (for [x v] [x (fresh)]))]
      (subst S t*))))

;;; unification

(defn unify [t1 t2]
  (cond
   (= t1 t2) {}
   ;;
   (type-var? t1)
   (when-not (contains? (ftv t2) t1) {t1 t2})
   ;;
   (type-var? t2)
   (when-not (contains? (ftv t1) t2) {t2 t1})
   ;;
   (every? sequential? [t1 t2])
   (let [[h1 & r1] t1
         [h2 & r2] t2
         S1 (unify h1 h2)
         S2 (unify (subst S1 r1) (subst S1 r2))]
     (compose S2 S1))
   ;;
   :else nil))

;;; W

(defn boolean? [o]
  (or (true? o) (false? o)))

(defn W [e env]
  (match e
    ;;
    (_ :guard integer?) [:int    {}]
    (_ :guard boolean?) [:bool   {}]
    (_ :guard string?)  [:string {}]
    ;;
    (_ :guard symbol?)
    (if-let [s (get env e)]
      [(instantiate s) {}]
      (throw (ex-info (str "Unbound variable: " e) {})))
    ;;
    ([] :seq)
    [(instantiate '(:forall #{a} (:list a))) {}]
    ;;
    (['fn [(x :guard symbol?)] e*] :seq)
    (let [beta    (fresh)
          [t1 S1] (W e* (assoc env x [:forall #{} beta]))]
      [(list (subst S1 beta) '-> t1) S1])
    ;;
    (['let [(x :guard symbol?) e1] e2] :seq)
    (let [[t1 S1] (W e1 env)
          cls     (generalize t1 env)
          [t2 S2] (W e2 (assoc env x cls))]
      [t2 (compose S2 S1)])
    ;;
    ([e1 e2] :seq)
    (let [[t1 S1] (W e1 env)
          [t2 S2] (W e2 (subst S1 env))
          S2#     (compose S2 S1)
          t3      (fresh)
          t4      (fresh)
          S3      (unify (subst S2# t1) (list t3 '-> t4))]
      (if-not S3
        (throw (ex-info (str "trying to apply non-function:\n\n"
                             " - irritant: " e1 "\n"
                             " - type:     " (reify t1) "\n") {}))
        (let [S3# (compose S3 S2 S1)
              S4  (unify (subst S3# t2) (subst S3# t3))]
          (if-not S4
            (throw (ex-info (str "wrong argument type:\n\n"
                                 " - function:      " e1 "\n"
                                 " - function type: " (reify t1) "\n"
                                 " - expected type: " (reify t3) "\n"
                                 " - argument type: " (reify t2) "\n"
                                 " - argument:      " e2 "\n") {}))
            [(subst S4 t4) (compose S4 S3 S2 S1)]))))))

;;; desugar

(defn desugar [e]
  (match e
    (['fn [x] t*] :seq)           (list 'fn [x] (desugar t*))
    (['fn [x & more] t*] :seq)    (desugar ['fn [x] ['fn more t*]])
    (['let [n v] t*] :seq)        (list 'let [n (desugar v)] (desugar t*))
    (['let [n v & more] t*] :seq) (desugar ['let [n v] ['let more t*]])
    ([x y] :seq)                  (list (desugar x) (desugar y))
    ([x y & more] :seq)           (desugar (cons [x y] more))
    :else                         e))

;;; reification

(defn type-var? [x]
  (and (symbol? x) (.startsWith (str x) "__type__")))

(defn reify [form]
  (let [counter (atom 0)
        vars    (transient {})]
    (postwalk (fn [x]
                (if (type-var? x)
                  (if-let [v (get vars x)]
                    v
                    (do
                      (let [v (symbol (str "t" @counter))]
                        (assoc! vars x v)
                        (swap! counter inc)
                        v)))
                  x))
              form)))

;;; type inference

(def ^:dynamic *default-type-env*
  {'+      '(:forall #{}  (:int -> (:int -> :int)))
   '-      '(:forall #{}  (:int -> (:int -> :int)))
   '*      '(:forall #{}  (:int -> (:int -> :int)))
   'if     '(:forall #{a} (:bool -> (a -> (a -> a))))
   'empty? '(:forall #{a} ((:list a) -> :bool))
   'cons   '(:forall #{a} (a -> ((:list a) -> (:list a))))
   'first  '(:forall #{a} ((:list a) -> a))
   'rest   '(:forall #{a} ((:list a) -> (:list a)))
   '=      '(:forall #{a} (a -> (a -> :bool)))
   'fix    '(:forall #{a} ((a -> a) -> a))})

(defn infer
  ([e]
   (infer e *default-type-env*))
  ([e env]
   (let [[t S] (W (desugar e) env)]
     (->> (subst S t) reify))))

;;; tests

(infer '+)
; => (:int -> (:int -> :int))
(infer '(+ 1 1))
; => :int
(infer '(fn [x] x))
; => (t0 -> t0)
(infer '(fn [x y] (+ x y)))
; => (:int -> (:int -> :int))
(infer '(let [f (fn [x] x)] f))
; => (t0 -> t0)
(infer '(if true 42 (+ 333 333)))
; => :int
(infer '())
; => (:list t0)
(infer '(empty? ()))
; :bool
(infer '(empty? (cons 1 ())))
; => :bool
(infer '(cons 1 ()))
; => (:list :int)
(infer '(first (cons 1 ())))
; => :int
(infer '(rest (cons 1 ())))
; => (:list :int)
(infer
 '(let [fact (fix
              (fn [fact x]
                (if (= x 1)
                  1
                  (* x (fact (- x 1))))))]
    (fact 10)))
; => :int

;; Tests used in `infer.ss` by Yin Wang
(infer '(fn [f x] (f x)))
; => ((t0 -> t1) -> (t0 -> t1))
(infer '(fn [f x] (f (f x))))
; => ((t0 -> t0) -> (t0 -> t0))
(infer '(fn [m n f x] ((m (n f)) x)))
;; => ((t0 -> (t1 -> t2)) -> ((t3 -> t0) -> (t3 -> (t1 -> t2))))
(infer '((fn [f] (f 1)) (fn [v] v)))
;; => :int
(def S '(fn [x y z] ((x z) (y z))))
(def K '(fn [x y] x))
(infer S)
; => ((t0 -> (t1 -> t2)) -> ((t0 -> t1) -> (t0 -> t2)))
(infer `(~S ~K))
; => ((t0 -> t1) -> (t0 -> t0))
(infer `((~S ~K) ~K))
; => (t0 -> t0)


;; one-liner to clear current namespace
;; (map #(ns-unmap *ns* %) (keys (ns-interns *ns*)))
