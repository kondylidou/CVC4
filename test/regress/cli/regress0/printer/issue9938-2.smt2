(set-logic ALL)
(set-info :status sat)
(declare-sort S 1)
(declare-datatype OptionS (par (Y) ( (none) (some (val (S Y))))))
(declare-const x (OptionS Int))
(declare-const y (OptionS Int))
(assert (= x y))
(check-sat)
(exit)
