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
(assert
  (and 
    (= nil nil)
    (tobool 
	(ssep
		(ls  x14 x9) 
		
		(ls  x9 x10) 
		
		(ls  x3 x2) 
		
		(pto x1 (ref f x4)) 
		
		(pto x13 (ref f x15)) 
		
		(pto x8 (ref f x9)) 
		
		(pto x2 (ref f x1)) 
		
		(pto x11 (ref f x2)) 
		
		(pto x10 (ref f x11)) 
		
		(ls  x12 x3) 
		
		(pto x7 (ref f x1)) 
		
		(ls  x4 x9) 
		
		(pto x15 (ref f x7)) 
		
		(ls  x6 x15) 
		
		(pto x16 (ref f x1)) 
		
		(pto x5 (ref f x3)) 
		(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp)))
	) )
  )
)
(assert
  (not
        (tobool 
	(ssep
		(ls  x14 x9) 
		
		(ls  x16 x1) 
		
		(ls  x6 x15) 
		
		(ls  x5 x3) 
		
		(ls  x13 x15) 
		
		(ls  x12 x1) 
		
		(ls  x8 x9) 
		
		(ls  x15 x2) 
		(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp)))
	) )
  ))

(check-sat)
