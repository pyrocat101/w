# Algorithm W

An implementation of algorithm W for Hindley-Milner polymorphic type inference.

Use the Source, Luke!

``` clojure
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
```

## References

1. Martin Grabmüller, Algorithm W Step by Step
2. Luis Damas and Robin Milner, Principal Type-Schemes for Functional Programs

## License

Copyright © 2014 Linjie Ding

Distributed under the Eclipse Public License either version 1.0 or (at your
option) any later version.
