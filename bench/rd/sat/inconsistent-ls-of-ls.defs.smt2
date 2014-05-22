cat: set-info.defs.smt2: No such file or directory

;generic sort 

(declare-sort GTyp 0)

;generic fields 
(declare-fun f0 () (Field GTyp GTyp))
(declare-fun f1 () (Field GTyp GTyp))

;predicates 

(define-fun P ((?x GTyp)) Space 
(tospace (or 

	(= nil ?x)


	(and (distinct nil ?x)
		 (tobool (Q ?x ?x)
		)
	)
))
)


(define-fun Q ((?x GTyp) (?y GTyp)) Space 
(tospace (or 

	(exists ((?d GTyp) (?c GTyp))
		
		 (and (= nil ?y)
		(distinct nil ?x)
			(tobool 
	(ssep (pto ?x (sref  (ref f0 ?d)  (ref f1 ?c) ))
		(P ?d)
	)

		))
	)


	(exists ((?d GTyp) (?c GTyp))
		
		 (and (distinct nil ?y)
			(tobool 
	(ssep (pto ?y (sref  (ref f0 ?d)  (ref f1 ?c) ))
		(Q ?x ?c)
	)

		))
	)
))
)


;vars 

;problem 
(declare-fun x0 () GTyp)

(assert (tobool (P  x0)))

(check-sat)

;;pto 2

;;pto 2
