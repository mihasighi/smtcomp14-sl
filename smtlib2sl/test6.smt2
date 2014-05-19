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
(assert
  (and 
    (= nil nil)
(distinct nil x1 )
    (tobool  (ssep  (ls x2 nil ) (ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp)))))
  )
)
(assert
  (not
    (and (= x2 x2 )
    (tobool (ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp))))
)  ))

(check-sat)
