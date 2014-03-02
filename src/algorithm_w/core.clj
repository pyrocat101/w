(ns algorithm-w.core
  (:use [clojure.core.match :only (match)]
        [clojure.set :only (union difference)]))

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
    [:forall vars τ] (difference (ftv τ) vars)))

(defn fresh-var [] (gensym))

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
    [:forall vars τ] [:forall vars (apply-subst (dissoc S vars) τ)]))

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

(defn instantiate
  ([σ env]
   (instantiate σ))
  ([σ]
   (match (vec σ)
     [:forall vars τ]
     (let [S (into {} (for [v vars] [v (fresh-var)]))]
       (apply-subst S τ)))))

;; unification

(defn cannot-unify [t1 t2]
  (Exception. (str "Cannot unify: " t1 " & " t2)))

(defn circular-unify [t1 t2]
  (Exception. (str "Cicrcular unify: " t1 " & " t2)))

(derive java.lang.Object ::_)

(defmulti unify (fn [x y] [(type x) (type y)]))

(defmethod unify [::type-var ::type-var] [t1 t2] {})

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
  (match [t1 t2]
    [[x1 '-> y1] [x2 '-> y2]] (let [S1 (unify x1 x2)
                                    S2 (unify (apply-subst S1 y1)
                                              (apply-subst S1 y2))]
                                (compose S2 S1))
    :else (throw (cannot-unify t1 t2))))

(prefer-method unify [::type-var ::type-var] [::type-var ::_])
(prefer-method unify [::type-var ::type-var] [::_ ::type-var])
(prefer-method unify [::type-var ::_]        [::_ ::type-var])

;;; W

(derive clojure.lang.Symbol ::var)
(derive java.lang.Integer   ::int)
(derive java.lang.Long      ::int)
(derive java.lang.Boolean   ::bool)

(defmulti W (fn [x y] (type x)))

(defmethod W ::var [v env]
  (if-let [σ (get env v)]
    [(instantiate σ) {}]
    (throw (Exception. (str "Unbound variable: " v)))))

(defmethod W ::int  [e env] [:int  {}])
(defmethod W ::bool [e env] [:bool {}])

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

;;; type inference

(def ^:dynamic *default-type-env*
  {'+ '[:forall #{} [:int -> [:int -> :int]]]})

(defn infer
  ([e]
   (infer e *default-type-env*))
  ([e env]
   (let [[t S] (W e env)]
     (apply-subst S t))))

;;; tests

(infer '+)
(infer '(+ 1))
(infer '(fn [x] x))
(infer '(fn [x] ((+ x) x)))
(infer '(let [f (fn [x] x)] f))

;; one-liner to clear current namespace
;; (map #(ns-unmap *ns* %) (keys (ns-interns *ns*)))
