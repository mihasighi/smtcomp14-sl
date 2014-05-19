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


(define-fun bool ((?x GTyp)) Space 
(tospace (or 
(tobool (zero ?x))
(tobool (one ?x))))
)


(define-fun bitvector ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?x23 GTyp) (?x24 GTyp) (?x25 GTyp) (?x26 GTyp) (?x27 GTyp) (?x28 GTyp) (?x29 GTyp)) Space 

	(ssep (bool ?x1)
		(bool ?x2)
		(bool ?x3)
		(bool ?x4)
		(bool ?x5)
		(bool ?x6)
		(bool ?x7)
		(bool ?x8)
		(bool ?x9)
		(bool ?x10)
		(bool ?x11)
		(bool ?x12)
		(bool ?x13)
		(bool ?x14)
		(bool ?x15)
		(bool ?x16)
		(bool ?x17)
		(bool ?x18)
		(bool ?x19)
		(bool ?x20)
		(bool ?x21)
		(bool ?x22)
		(bool ?x23)
		(bool ?x24)
		(bool ?x25)
		(bool ?x26)
		(bool ?x27)
		(bool ?x28)
		(bool ?x29)
	)
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
(declare-fun x28 () GTyp)

(assert (tobool (bitvector  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28)))

(check-sat)
