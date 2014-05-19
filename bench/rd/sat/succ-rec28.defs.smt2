(set-logic QF_S)
(set-info :source |
  James Brotherston, Carsten Fuhs, Nikos Gorogiannis, and Juan Navarro Pérez.
  A decision procedure for satisfiability in separation logic with inductive
  predicates. To appear at CSL-LICS, 2014.
  https://github.com/ngorogiannis/cyclist
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unknown)



;generic sort 

(declare-sort GTyp 0)

;generic fields 
(declare-fun f0 () (Field GTyp GTyp))
(declare-fun f1 () (Field GTyp GTyp))

;predicates 

(define-fun zero ((?x GTyp)) Space 

	(tospace (= nil ?x))
)


(define-fun one ((?x GTyp)) Space 

	(tospace (distinct nil ?x))
)


(define-fun succ28rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?x23 GTyp) (?x24 GTyp) (?x25 GTyp) (?x26 GTyp) (?x27 GTyp) (?x28 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp) (?y21 GTyp) (?y22 GTyp) (?y23 GTyp) (?y24 GTyp) (?y25 GTyp) (?y26 GTyp) (?y27 GTyp) (?y28 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		(= ?x20 ?y20)
		(= ?x21 ?y21)
		(= ?x22 ?y22)
		(= ?x23 ?y23)
		(= ?x24 ?y24)
		(= ?x25 ?y25)
		(= ?x26 ?y26)
		(= ?x27 ?y27)
		(= ?x28 ?y28)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ27rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26 ?y27 ?y28)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ27rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?x23 GTyp) (?x24 GTyp) (?x25 GTyp) (?x26 GTyp) (?x27 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp) (?y21 GTyp) (?y22 GTyp) (?y23 GTyp) (?y24 GTyp) (?y25 GTyp) (?y26 GTyp) (?y27 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		(= ?x20 ?y20)
		(= ?x21 ?y21)
		(= ?x22 ?y22)
		(= ?x23 ?y23)
		(= ?x24 ?y24)
		(= ?x25 ?y25)
		(= ?x26 ?y26)
		(= ?x27 ?y27)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ26rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26 ?y27)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ26rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?x23 GTyp) (?x24 GTyp) (?x25 GTyp) (?x26 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp) (?y21 GTyp) (?y22 GTyp) (?y23 GTyp) (?y24 GTyp) (?y25 GTyp) (?y26 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		(= ?x20 ?y20)
		(= ?x21 ?y21)
		(= ?x22 ?y22)
		(= ?x23 ?y23)
		(= ?x24 ?y24)
		(= ?x25 ?y25)
		(= ?x26 ?y26)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ25rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ25rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?x23 GTyp) (?x24 GTyp) (?x25 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp) (?y21 GTyp) (?y22 GTyp) (?y23 GTyp) (?y24 GTyp) (?y25 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		(= ?x20 ?y20)
		(= ?x21 ?y21)
		(= ?x22 ?y22)
		(= ?x23 ?y23)
		(= ?x24 ?y24)
		(= ?x25 ?y25)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ24rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ24rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?x23 GTyp) (?x24 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp) (?y21 GTyp) (?y22 GTyp) (?y23 GTyp) (?y24 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		(= ?x20 ?y20)
		(= ?x21 ?y21)
		(= ?x22 ?y22)
		(= ?x23 ?y23)
		(= ?x24 ?y24)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ23rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ23rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?x23 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp) (?y21 GTyp) (?y22 GTyp) (?y23 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		(= ?x20 ?y20)
		(= ?x21 ?y21)
		(= ?x22 ?y22)
		(= ?x23 ?y23)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ22rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ22rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp) (?y21 GTyp) (?y22 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		(= ?x20 ?y20)
		(= ?x21 ?y21)
		(= ?x22 ?y22)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ21rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ21rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp) (?y21 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		(= ?x20 ?y20)
		(= ?x21 ?y21)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ20rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ20rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		(= ?x20 ?y20)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ19rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ19rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ18rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ18rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ17rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ17rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ16rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ16rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ15rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ15rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ14rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ14rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ13rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ13rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ12rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ12rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ11rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ11rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ10rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ10rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ9rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ9rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ8rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ8rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ7rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ7rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ6rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ6rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ5rec ?x2 ?x3 ?x4 ?x5 ?x6 ?y2 ?y3 ?y4 ?y5 ?y6)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ5rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ4rec ?x2 ?x3 ?x4 ?x5 ?y2 ?y3 ?y4 ?y5)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ4rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ3rec ?x2 ?x3 ?x4 ?y2 ?y3 ?y4)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ3rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ2rec ?x2 ?x3 ?y2 ?y3)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ2rec ((?x1 GTyp) (?x2 GTyp) (?y1 GTyp) (?y2 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ1rec ?x2 ?y2)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ1rec ((?x1 GTyp) (?y1 GTyp)) Space 

	(ssep (zero ?x1)
		(one ?y1)
	)
)


(define-fun P ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?x23 GTyp) (?x24 GTyp) (?x25 GTyp) (?x26 GTyp) (?x27 GTyp) (?x28 GTyp)) Space 

	(ssep (one ?x1)
		(one ?x2)
		(one ?x3)
		(one ?x4)
		(one ?x5)
		(one ?x6)
		(one ?x7)
		(one ?x8)
		(one ?x9)
		(one ?x10)
		(one ?x11)
		(one ?x12)
		(one ?x13)
		(one ?x14)
		(one ?x15)
		(one ?x16)
		(one ?x17)
		(one ?x18)
		(one ?x19)
		(one ?x20)
		(one ?x21)
		(one ?x22)
		(one ?x23)
		(one ?x24)
		(one ?x25)
		(one ?x26)
		(one ?x27)
		(one ?x28)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28)
	)
)


(define-fun Q ((?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp) (?y21 GTyp) (?y22 GTyp) (?y23 GTyp) (?y24 GTyp) (?y25 GTyp) (?y26 GTyp) (?y27 GTyp) (?y28 GTyp)) Space 
(tospace (or 
(tobool 
	(ssep (zero ?y1)
		(zero ?y2)
		(zero ?y3)
		(zero ?y4)
		(zero ?y5)
		(zero ?y6)
		(zero ?y7)
		(zero ?y8)
		(zero ?y9)
		(zero ?y10)
		(zero ?y11)
		(zero ?y12)
		(zero ?y13)
		(zero ?y14)
		(zero ?y15)
		(zero ?y16)
		(zero ?y17)
		(zero ?y18)
		(zero ?y19)
		(zero ?y20)
		(zero ?y21)
		(zero ?y22)
		(zero ?y23)
		(zero ?y24)
		(zero ?y25)
		(zero ?y26)
		(zero ?y27)
		(zero ?y28)
	)
)

	(exists ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?x23 GTyp) (?x24 GTyp) (?x25 GTyp) (?x26 GTyp) (?x27 GTyp) (?x28 GTyp))
		
		 (tobool 
	(ssep (succ28rec ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26 ?y27 ?y28)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28)
	)

		)
	)
))
)


;vars 

;problem 
(declare-fun x0 () GTyp)
(declare-fun x1 () GTyp)
(declare-fun x2 () GTyp)
(declare-fun x3 () GTyp)
(declare-fun x4 () GTyp)
(declare-fun x5 () GTyp)
(declare-fun x6 () GTyp)
(declare-fun x7 () GTyp)
(declare-fun x8 () GTyp)
(declare-fun x9 () GTyp)
(declare-fun x10 () GTyp)
(declare-fun x11 () GTyp)
(declare-fun x12 () GTyp)
(declare-fun x13 () GTyp)
(declare-fun x14 () GTyp)
(declare-fun x15 () GTyp)
(declare-fun x16 () GTyp)
(declare-fun x17 () GTyp)
(declare-fun x18 () GTyp)
(declare-fun x19 () GTyp)
(declare-fun x20 () GTyp)
(declare-fun x21 () GTyp)
(declare-fun x22 () GTyp)
(declare-fun x23 () GTyp)
(declare-fun x24 () GTyp)
(declare-fun x25 () GTyp)
(declare-fun x26 () GTyp)
(declare-fun x27 () GTyp)

(assert (tobool (P  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)))

(check-sat)
