(ns algorithm-w.core
  (:use [clojure.core.match :only (match)]
        [clojure.set :only (union difference)]
        [clojure.walk :only (postwalk)]))

(defn mapval [f m]
  (into {} (for [[k v] m] [k (f v)])))

(derive clojure.lang.IPersistentMap ::type-env)
(derive clojure.lang.Keyword        ::type-const)
(derive clojure.lang.Symbol         ::type-var)

;;; free type variable

(defmulti ftv type)

(defmethod ftv ::type-env [env]
  (apply union (map ftv (vals env))))

(defmethod ftv ::type-const [t] #{})
(defmethod ftv ::type-var   [t] #{t})

(defmethod ftv :default [t]
  (match (vec t)
    [t1 '-> t2]      (union (ftv t1) (ftv t2))
    [:forall vars τ] (difference (ftv τ) vars)
    [_ & τs]         (apply union (map ftv τs))))

(defn fresh-var [] (gensym "__type__"))

(defn type-var? [x]
  (and (symbol? x) (.startsWith (str x) "__type__")))

;;; substitution

(defmulti apply-subst (fn [x y] (type y)))

(defmethod apply-subst ::type-env [S env]
  (mapval #(apply-subst S %) env))

(defmethod apply-subst ::type-const [S t] t)

(defmethod apply-subst ::type-var [S t]
  (if-let [t (S t)] t t))

(defmethod apply-subst :default [S t]
  (match (vec t)
    [t1 '-> t2]      [(apply-subst S t1) '-> (apply-subst S t2)]
    [:forall vars τ] [:forall vars (apply-subst (dissoc S vars) τ)]
    [n & τs]         (cons n (map #(apply-subst S %) τs))))

(defn compose
  "Compose type substitutions, right-to-left, i.e. should have
   apply (compose s1 s2) t = apply s1 (apply s2 t)"
  ([s1 s2]
   (merge (apply-subst s1 s2) s1))
  ([s1 s2 & more]
   (compose s1 (apply compose (cons s2 more)))))

;;; generalize/instantiate

(defn generalize [τ env]
  [:forall (difference (ftv τ) (ftv env)) τ])

(defn instantiate [σ]
  (match (vec σ)
    [:forall vars τ]
    (let [S (into {} (for [v vars] [v (fresh-var)]))]
      (apply-subst S τ))))

;; unification

(defn cannot-unify [t1 t2]
  (Exception. (str "Cannot unify: " t1 " & " t2)))

(defn circular-unify [t1 t2]
  (Exception. (str "Cicrcular unify: " t1 " & " t2)))

(derive java.lang.Object ::_)

(defmulti unify (fn [x y] [(type x) (type y)]))

(defmethod unify [::type-var ::_] [t1 t2]
  (if (contains? (ftv t2) t1)
    (throw (circular-unify t1 t2))
    {t1 t2}))

(defmethod unify [::_ ::type-var] [t1 t2]
  (unify t2 t1))

(defmethod unify [::type-const ::type-const] [t1 t2]
  (if (= t1 t2)
    {}
    (throw (cannot-unify t1 t2))))

(defmethod unify :default [t1 t2]
  (match [(vec t1) (vec t2)]
    [[x1 '-> y1] [x2 '-> y2]]
    (let [S1 (unify x1 x2)
          S2 (unify (apply-subst S1 y1) (apply-subst S1 y2))]
      (compose S2 S1))
    [[n1 & τs1] [n2 & τs2]]
    (if (and (= n1 n2) (= (count τs1) (count τs2)))
      (reduce (fn [S1 [τ1 τ2]]
                (let [S2 (unify (apply-subst S1 τ1)
                                (apply-subst S1 τ2))]
                  (compose S2 S1)))
              {}
              (map vector τs1 τs2))
      (throw (cannot-unify t1 t2)))
    :else (throw (cannot-unify t1 t2))))

(prefer-method unify [::type-var ::_] [::_ ::type-var])

;;; W

(derive clojure.lang.Symbol ::var)
(derive java.lang.Integer   ::int)
(derive java.lang.Long      ::int)
(derive java.lang.Boolean   ::bool)

(defmulti W
  (fn [x y]
    (if (and (seq? x) (empty? x))
      ::nil
      (type x))))

(defmethod W ::var [v env]
  (if-let [σ (get env v)]
    [(instantiate σ) {}]
    (throw (Exception. (str "Unbound variable: " v)))))

(defmethod W ::int  [e env] [:int  {}])
(defmethod W ::bool [e env] [:bool {}])

(defmethod W ::nil  [e env]
  [(instantiate '[:forall #{a} [:list a]]) {}])

(defmethod W :default [e env]
  (match (vec e)
    [e1 e2] (let [[t1 S1] (W e1 env)
                  [t2 S2] (W e2 (apply-subst S1 env))
                  β       (fresh-var)
                  S3      (unify (apply-subst S2 t1) [t2 '-> β])]
              [(apply-subst S3 β) (compose S3 S2 S1)])
    ['fn [x] e1] (let [β       (fresh-var)
                       [t1 S1] (W e1 (assoc env x [:forall #{} β]))]
                   [[(apply-subst S1 β) '-> t1] S1])
    ['let [x e1] e2] (let [[t1 S1] (W e1 env)
                           closure (generalize t1 env)
                           [t2 S2] (W e2 (assoc env x closure))]
                       [t2 (compose S2 S1)])))

;;; desugar

(derive clojure.lang.ISeq ::list)
(derive clojure.lang.IPersistentVector ::list)

(defmulti desugar type)

(defmethod desugar ::list [e]
  (match (vec e)
    ['fn [x] body]           ['fn [x] (desugar body)]
    ['fn [x & more] body]    (desugar ['fn [x] ['fn more body]])
    ['let [n v] body] ['let  [n (desugar v)] (desugar body)]
    ['let [n v & more] body] (desugar ['let [n v] ['let more body]])
    [x y]                    [(desugar x) (desugar y)]
    [x y & more]             (desugar (cons [x y] more))
    :else e))

(defmethod desugar :default [e] e)

;;; type pretty-print

(defn pretty-print [form]
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
  {'+      '[:forall #{}  [:int -> [:int -> :int]]]
   '-      '[:forall #{}  [:int -> [:int -> :int]]]
   '*      '[:forall #{}  [:int -> [:int -> :int]]]
   'if     '[:forall #{a} [:bool -> [a -> [a -> a]]]]
   'empty? '[:forall #{a} [[:list a] -> :bool]]
   'cons   '[:forall #{a} [a -> [[:list a] -> [:list a]]]]
   'first  '[:forall #{a} [[:list a] -> a]]
   'rest   '[:forall #{a} [[:list a] -> [:list a]]]
   '=      '[:forall #{a} [a -> [a -> :bool]]]
   'fix    '[:forall #{a} [[a -> a] -> a]]})

(defn infer
  ([e]
   (infer e *default-type-env*))
  ([e env]
   (let [[t S] (W (desugar e) env)]
     (->> (apply-subst S t)
          (pretty-print)))))

;;; tests

(infer '+)
; => [:int -> [:int -> :int]]
(infer '(+ 1 1))
; => :int
(infer '(fn [x] x))
; => [t0 -> t0]
(infer '(fn [x y] (+ x y)))
; => [:int -> [:int -> :int]]
(infer '(let [f (fn [x] x)] f))
; => [t0 -> t0]
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
; => [[t0 -> t1] -> [t0 -> t1]]
(infer '(fn [f x] (f (f x))))
; => [[t0 -> t0] -> [t0 -> t0]]
(infer '(fn [m n f x] ((m (n f)) x)))
;; => [[t0 -> [t1 -> t2]] -> [[t3 -> t0] -> [t3 -> [t1 -> t2]]]]
(infer '((fn [f] (f 1)) (fn [v] v)))
;; => :int
(def S '(fn [x y z] ((x z) (y z))))
(def K '(fn [x y] x))
(infer S)
; => [[t0 -> [t1 -> t2]] -> [[t0 -> t1] -> [t0 -> t2]]]
(infer `(~S ~K))
; => [[t0 -> t1] -> [t0 -> t0]]
(infer `((~S ~K) ~K))
; => [t0 -> t0]


;; one-liner to clear current namespace
;; (map #(ns-unmap *ns* %) (keys (ns-interns *ns*)))
