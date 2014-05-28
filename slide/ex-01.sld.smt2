
(set-logic QF_S)
(set-info :source |
  R. Iosif, A. Rogalewicz and T. Vojnar.
  Deciding Entailments in Inductive Separation Logic with Tree  Automata arXiv:1402.2127.
  http://www.fit.vutbr.cz/research/groups/verifit/tools/slide/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unknown)

;generic sort

(declare-sort TLL_t 0)

;generic fields

(declare-fun left () (Field TLL_t TLL_t))
(declare-fun right () (Field TLL_t TLL_t))
(declare-fun next () (Field TLL_t TLL_t))
(declare-fun parent () (Field TLL_t TLL_t))

(define-fun points_to ((?a TLL_t) (?b TLL_t) (?c TLL_t) (?d TLL_t) (?e  TLL_t)) Space
	    (pto ?a (sref (ref left ?b) (ref right ?c) (ref parent ?d) (ref  next ?e)))
)

;; tll(root,par,ll,lr) ::= root->nil,nil,par,lr & root=ll
;;	|\E l,r,z . root->l,r,par,nil * tll(l,root,ll,z) * tll(r,root,z,lr)

(define-fun TLL_plus ((?root TLL_t) (?par TLL_t) (?ll TLL_t) (?lr  TLL_t)) Space
  (tospace (or
    (and (tobool (points_to ?root nil nil ?par ?lr) (= ?root ?ll)))
    (exists ((?l TLL_t) (?r TLL_t) (?z TLL_t)) (tobool (ssep  (points_to ?l ?r ?par nil)
    	    	 	    	       	       	       	     (TLL_plus ?l ?root ?ll ?z)
							     (TLL_plus ?r ?root ?z ?lr))))
)))

(declare-fun x () TLL_t)
(declare-fun y () TLL_t)
(declare-fun u () TLL_t)
(declare-fun v () TLL_t)

(assert (tobool (TLL_plus x y u v)
))

(assert (not (tobool
	(TLL_plus x y u v)
)))

(check-sat)

