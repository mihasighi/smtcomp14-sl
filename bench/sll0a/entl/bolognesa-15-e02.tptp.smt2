(set-logic QF_S)
(set-info :source |
A. Rybalchenko and J. A. Navarro Pérez.
[Separation Logic + Superposition Calculus = Heap Theorem Prover]
[PLDI 2011]
http://navarroj.com/research/papers.html#pldi11
|)
(set-info :smt-lib-version 2.0)
(set-info :category "random") 
(set-info :status unknown)
(set-info :version 2014-05-22)

(set-logic QF_NOLL)

(declare-sort Sll_t 0)

(declare-fun f () (Field Sll_t Sll_t))

(define-fun ls ((?in Sll_t) (?out Sll_t)) Space
(tospace (or (= ?in ?out)
(exists ((?u Sll_t))
(and (distinct ?in ?out) (tobool
(ssep (pto ?in (ref f ?u)) (ls ?u ?out)
)))))))

(declare-fun x_emp () Sll_t)
(declare-fun y_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun t_emp () Sll_t)
(declare-fun x0 () Sll_t)
(declare-fun x1 () Sll_t)
(declare-fun x2 () Sll_t)
(declare-fun x3 () Sll_t)
(declare-fun x4 () Sll_t)
(declare-fun x5 () Sll_t)
(declare-fun x6 () Sll_t)
(declare-fun x7 () Sll_t)
(declare-fun x8 () Sll_t)
(declare-fun x9 () Sll_t)
(declare-fun x10 () Sll_t)
(declare-fun x11 () Sll_t)
(declare-fun x12 () Sll_t)
(declare-fun x13 () Sll_t)
(declare-fun x14 () Sll_t)
(declare-fun x15 () Sll_t)
(declare-fun x16 () Sll_t)
(declare-fun x17 () Sll_t)
(declare-fun x18 () Sll_t)
(declare-fun x19 () Sll_t)
(assert
  (and 
    (= nil nil)
    (tobool  (ssep  (ls x11 x14 ) (ssep  (pto x4  (ref f x9 ) ) (ssep  (pto x2  (ref f x5 ) ) (ssep  (pto x3  (ref f x12 ) ) (ssep  (ls x14 x11 ) (ssep  (ls x10 x13 ) (ssep  (pto x6  (ref f x2 ) ) (ssep  (pto x15  (ref f x6 ) ) (ssep  (pto x7  (ref f x5 ) ) (ssep  (pto x1  (ref f x13 ) ) (ssep  (pto x5  (ref f x1 ) ) (ssep  (pto x13  (ref f x12 ) ) (ssep  (pto x8  (ref f x12 ) ) (ssep  (ls x12 x5 ) (ssep  (ls x9 x8 )(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp)))))))))))))))))))
  )
)
(assert
  (not
        (tobool  (ssep  (ls x15 x6 ) (ssep  (ls x10 x13 ) (ssep  (ls x6 x2 ) (ssep  (ls x3 x12 ) (ssep  (ls x4 x9 ) (ssep  (ls x2 x5 ) (ssep  (ls x9 x8 ) (ssep  (ls x13 x12 ) (ssep  (ls x7 x5 ) (ssep  (ls x8 x13 ) (ssep  (ls x14 x11 ) (ssep  (ls x11 x14 )(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp))))))))))))))))
  ))

(check-sat)
