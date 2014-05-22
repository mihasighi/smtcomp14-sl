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

(declare-fun nil () Sll_t)

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
(declare-fun x20 () Sll_t)
(assert
  (and 
    (= nil nil)
    (tobool  (ssep  (ls x15 x7 ) (ssep  (pto x11  (ref f x2 ) ) (ssep  (pto x13  (ref f x12 ) ) (ssep  (ls x5 x14 ) (ssep  (pto x6  (ref f x16 ) ) (ssep  (pto x10  (ref f x16 ) ) (ssep  (pto x16  (ref f x9 ) ) (ssep  (pto x8  (ref f x15 ) ) (ssep  (ls x3 x13 ) (ssep  (ls x2 x6 ) (ssep  (pto x12  (ref f x16 ) ) (ssep  (ls x9 x7 ) (ssep  (pto x4  (ref f x10 ) ) (ssep  (pto x14  (ref f x11 ) ) (ssep  (pto x1  (ref f x6 ) ) (ssep  (pto x7  (ref f x14 ) )(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp))))))))))))))))))))
  )
)
(assert
  (not
        (tobool  (ssep  (ls x8 x7 ) (ssep  (ls x4 x10 ) (ssep  (ls x5 x11 ) (ssep  (ls x3 x12 ) (ssep  (ls x12 x16 ) (ssep  (ls x1 x6 ) (ssep  (ls x10 x16 ) (ssep  (ls x11 x14 )(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp))))))))))))
  ))

(check-sat)