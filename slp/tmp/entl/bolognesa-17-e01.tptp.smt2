(set-logic QF_S)
(set-info :source |
A. Rybalchenko and J. A. Navarro Perez.
[Separation Logic + Superposition Calculus = Heap Theorem Prover]
[PLDI 2011]
http://navarroj.com/research/papers.html#pldi11
|)
(set-info :smt-lib-version 2.0)
(set-info :category "random") 
(set-info :status unknown)
(set-info :version "2014-05-28")

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
(declare-fun x20 () Sll_t)
(declare-fun x21 () Sll_t)
(assert
  (and 
    (= nil nil)
    (tobool 
	(ssep
		(pto x7 (ref f x2)) 
		
		(pto x6 (ref f x11)) 
		
		(pto x12 (ref f x4)) 
		
		(ls  x9 x10) 
		
		(pto x10 (ref f x13)) 
		
		(pto x8 (ref f x7)) 
		
		(pto x11 (ref f x13)) 
		
		(pto x5 (ref f x9)) 
		
		(pto x16 (ref f x14)) 
		
		(pto x1 (ref f x10)) 
		
		(pto x14 (ref f x6)) 
		
		(pto x17 (ref f x7)) 
		
		(ls  x2 x3) 
		
		(pto x13 (ref f x5)) 
		
		(pto x3 (ref f x7)) 
		
		(pto x4 (ref f x12)) 
		
		(ls  x15 x2) 
		(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp)))
	) )
  )
)
(assert
  (not
        (tobool 
	(ssep
		(ls  x16 x14) 
		
		(ls  x1 x10) 
		
		(ls  x15 x2) 
		
		(ls  x3 x7) 
		
		(ls  x10 x13) 
		
		(ls  x12 x4) 
		
		(ls  x17 x7) 
		
		(ls  x14 x6) 
		
		(ls  x4 x12) 
		
		(ls  x6 x13) 
		
		(ls  x8 x3) 
		
		(ls  x13 x10) 
		(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp)))
	) )
  ))

(check-sat)