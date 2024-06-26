; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const c0 (_ BitVec 1))
(declare-const c1 (_ BitVec 1))
(declare-const t0 (_ BitVec 4))
(declare-const t1 (_ BitVec 4))
(declare-const e0 (_ BitVec 4))
(declare-const e1 (_ BitVec 4))
(assert (not (=
	(bvite c0 t0 (bvite c1 t1 t0))
	(bvite (bvand (bvnot c0) c1) t1 t0)
	)))
(check-sat)
(exit)
