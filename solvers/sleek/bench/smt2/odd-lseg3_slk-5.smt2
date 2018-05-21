(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun olseg ((?in node) (?p node))
Space (tospace
(or
(and 
(tobool  
(pto ?in  (ref nxt ?p))
 )
)(exists ((?a node)(?b node))(and 
(tobool (ssep 
(pto ?in  (ref nxt ?a))
(pto ?a  (ref nxt ?b))
(olseg ?b ?p)
) )
)))))











(declare-fun p () node)
(declare-fun a () node)
(declare-fun b () node)


(assert 
(and 
(tobool (ssep 
(olseg b p)
(pto p  (ref nxt a))
(pto a  (ref nxt b))
) )
)
)

(assert (not 
(and 
(tobool  
(olseg b b)
 )
)
))

(check-sat)