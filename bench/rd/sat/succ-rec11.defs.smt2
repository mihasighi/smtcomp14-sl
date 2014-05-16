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
 

	(= nil ?x)

 )


(define-fun one ((?x GTyp)) Space 
 

	(distinct nil ?x)

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
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ10rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11)
		(one ?x1)
		(zero ?y1)
	)

) )
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
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ9rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10)
		(one ?x1)
		(zero ?y1)
	)

) )
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
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ8rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9)
		(one ?x1)
		(zero ?y1)
	)

) )
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
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ7rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8)
		(one ?x1)
		(zero ?y1)
	)

) )
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
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ6rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7)
		(one ?x1)
		(zero ?y1)
	)

) )
 )


(define-fun succ6rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		 (tobool 
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ5rec ?x2 ?x3 ?x4 ?x5 ?x6 ?y2 ?y3 ?y4 ?y5 ?y6)
		(one ?x1)
		(zero ?y1)
	)

) )
 )


(define-fun succ5rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		 (tobool 
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ4rec ?x2 ?x3 ?x4 ?x5 ?y2 ?y3 ?y4 ?y5)
		(one ?x1)
		(zero ?y1)
	)

) )
 )


(define-fun succ4rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		 (tobool 
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ3rec ?x2 ?x3 ?x4 ?y2 ?y3 ?y4)
		(one ?x1)
		(zero ?y1)
	)

) )
 )


(define-fun succ3rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		 (tobool 
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ2rec ?x2 ?x3 ?y2 ?y3)
		(one ?x1)
		(zero ?y1)
	)

) )
 )


(define-fun succ2rec ((?x1 GTyp) (?x2 GTyp) (?y1 GTyp) (?y2 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		 (tobool 
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ1rec ?x2 ?y2)
		(one ?x1)
		(zero ?y1)
	)

) )
 )


(define-fun succ1rec ((?x1 GTyp) (?y1 GTyp)) Space 
 

	(sep (zero ?x1)
		(one ?y1)
	)

 )


(define-fun P ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp)) Space 
 

	(sep (one ?x1)
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
		(Q ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11)
	)

 )


(define-fun Q ((?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp)) Space 
(tospace (or 

	(sep (zero ?y1)
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
	)


	(exists ((?x1 GenTyp) (?x2 GenTyp) (?x3 GenTyp) (?x4 GenTyp) (?x5 GenTyp) (?x6 GenTyp) (?x7 GenTyp) (?x8 GenTyp) (?x9 GenTyp) (?x10 GenTyp) (?x11 GenTyp))
		
		 (tobool 
	(sep (succ11rec ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11)
	)

		)
	)

) )
 )


;index vars 
(define-fun alpha1 () SetLoc)

;vars 

;problem 
;;(define-fun x0 () GenTyp)
;;(assert (tobool (index alpha1 (zero  x0))))
;;(define-fun x0 () GenTyp)
;;(assert (tobool (index alpha1 (one  x0))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(define-fun x8 () GenTyp)
;;(define-fun x9 () GenTyp)
;;(define-fun x10 () GenTyp)
;;(define-fun x11 () GenTyp)
;;(define-fun x12 () GenTyp)
;;(define-fun x13 () GenTyp)
;;(define-fun x14 () GenTyp)
;;(define-fun x15 () GenTyp)
;;(define-fun x16 () GenTyp)
;;(define-fun x17 () GenTyp)
;;(define-fun x18 () GenTyp)
;;(define-fun x19 () GenTyp)
;;(define-fun x20 () GenTyp)
;;(define-fun x21 () GenTyp)
;;(assert (tobool (index alpha1 (succ11rec  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(define-fun x8 () GenTyp)
;;(define-fun x9 () GenTyp)
;;(define-fun x10 () GenTyp)
;;(define-fun x11 () GenTyp)
;;(define-fun x12 () GenTyp)
;;(define-fun x13 () GenTyp)
;;(define-fun x14 () GenTyp)
;;(define-fun x15 () GenTyp)
;;(define-fun x16 () GenTyp)
;;(define-fun x17 () GenTyp)
;;(define-fun x18 () GenTyp)
;;(define-fun x19 () GenTyp)
;;(assert (tobool (index alpha1 (succ10rec  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(define-fun x8 () GenTyp)
;;(define-fun x9 () GenTyp)
;;(define-fun x10 () GenTyp)
;;(define-fun x11 () GenTyp)
;;(define-fun x12 () GenTyp)
;;(define-fun x13 () GenTyp)
;;(define-fun x14 () GenTyp)
;;(define-fun x15 () GenTyp)
;;(define-fun x16 () GenTyp)
;;(define-fun x17 () GenTyp)
;;(assert (tobool (index alpha1 (succ9rec  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(define-fun x8 () GenTyp)
;;(define-fun x9 () GenTyp)
;;(define-fun x10 () GenTyp)
;;(define-fun x11 () GenTyp)
;;(define-fun x12 () GenTyp)
;;(define-fun x13 () GenTyp)
;;(define-fun x14 () GenTyp)
;;(define-fun x15 () GenTyp)
;;(assert (tobool (index alpha1 (succ8rec  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(define-fun x8 () GenTyp)
;;(define-fun x9 () GenTyp)
;;(define-fun x10 () GenTyp)
;;(define-fun x11 () GenTyp)
;;(define-fun x12 () GenTyp)
;;(define-fun x13 () GenTyp)
;;(assert (tobool (index alpha1 (succ7rec  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(define-fun x8 () GenTyp)
;;(define-fun x9 () GenTyp)
;;(define-fun x10 () GenTyp)
;;(define-fun x11 () GenTyp)
;;(assert (tobool (index alpha1 (succ6rec  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(define-fun x8 () GenTyp)
;;(define-fun x9 () GenTyp)
;;(assert (tobool (index alpha1 (succ5rec  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(assert (tobool (index alpha1 (succ4rec  x0 x1 x2 x3 x4 x5 x6 x7))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(assert (tobool (index alpha1 (succ3rec  x0 x1 x2 x3 x4 x5))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(assert (tobool (index alpha1 (succ2rec  x0 x1 x2 x3))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(assert (tobool (index alpha1 (succ1rec  x0 x1))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(define-fun x8 () GenTyp)
;;(define-fun x9 () GenTyp)
;;(define-fun x10 () GenTyp)
;;(assert (tobool (index alpha1 (P  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))))
(define-fun x0 () GenTyp)
(define-fun x1 () GenTyp)
(define-fun x2 () GenTyp)
(define-fun x3 () GenTyp)
(define-fun x4 () GenTyp)
(define-fun x5 () GenTyp)
(define-fun x6 () GenTyp)
(define-fun x7 () GenTyp)
(define-fun x8 () GenTyp)
(define-fun x9 () GenTyp)
(define-fun x10 () GenTyp)
(assert (tobool (index alpha1 (Q  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))))



(check-sat)

