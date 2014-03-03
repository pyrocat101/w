# Algorithm W

An implementation of algorithm W for Hindley-Milner polymorphic type inference.

Use the Source, Luke!

``` clojure
(infer '+) ;; [:int -> [:int -> :int]]
(infer '(+ 1 1)) ;; :int
(infer '(fn [x] x)) ;; [G__9440 -> G__9440]
(infer '(fn [x y] (+ x y))) ;; [:int -> [:int -> :int]]
(infer '(let [f (fn [x] x)] f)) ;; [G__9450 -> G__9450]
(infer '(if true 42 (+ 333 333))) ;; :int
(infer '()) ;; (:list G__9461)
(infer '(empty? ())) ;; :bool
(infer '(empty? (cons 1 ()))) ;; :bool
(infer '(cons 1 ())) ;; (:list :int)
(infer '(first (cons 1 ()))) ;; :int
(infer '(rest (cons 1 ()))) ;; (:list :int)
```

## References

1. Martin Grabmüller, Algorithm W Step by Step
2. Luis Damas and Robin Milner, Principal Type-Schemes for Functional Programs

## License

Copyright © 2014 Linjie Ding

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.
