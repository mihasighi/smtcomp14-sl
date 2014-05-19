(set-logic QF_SLRD)

(declare-sort Sll_t 0)

(declare-fun f () (Field Sll_t Sll_t))

(define-fun ls ((?in Sll_t) (?out Sll_t)) Space
(tospace (or (= ?in ?out)
(exists ((?u Sll_t))
(tobool
(ssep (pto ?in (ref f ?u)) (ls ?u ?out)
))))))

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
(assert
  (and 
    (= nil nil)
(distinct nil x1 )
(distinct nil x2 )
(distinct nil x3 )
(distinct x1 x3 )
(distinct x2 x3 )
(distinct nil x5 )
(distinct nil x6 )
(distinct nil x7 )
(distinct x5 x7 )
(distinct x6 x7 )
    (tobool  (ssep  (ls x6 x5 ) (ssep  (pto x7  (ref f x6 ) ) (ssep  (pto x5  (ref f x7 ) ) (ssep  (ls x2 x1 ) (ssep  (pto x3  (ref f x2 ) ) (ssep  (pto x1  (ref f x3 ) )(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp))))))))))
  )
)
(assert
  (not
        (tobool  (ssep  (pto x8  (ref f x7 ) ) (ssep  (ls x6 x8 ) (ssep  (pto x7  (ref f x6 ) ) (ssep  (pto x4  (ref f x3 ) ) (ssep  (ls x2 x4 ) (ssep  (pto x3  (ref f x2 ) )(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp))))))))))
  ))

(check-sat)
